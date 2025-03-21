{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Effect.FlatCurry.Let where

import Curry.FlatCurry.Type (VarIndex)
import qualified Data.Map as Map
import Effect.General.Memoization
import Effect.General.State
import Signature
import Debug.Trace (trace)
import Type (analyzeVarIndex)

type Let sig sigl a =
    (Renaming :<: sig, Thunking a :<<<<: sigl)

lvar
    :: (Let sig sigl a, EffectCons m sig sigs sigl Id)
    => Ptr
    -> m a
lvar ptr = do
    logCall >> force ptr
{-# INLINE lvar #-}

let'
    :: (EffectCons m sig sigs sigl Id, Let sig sigl a)
    => [(VarIndex, m a)]
    -> m a
    -> m a
let' bs e =
    logCall >> do
        mapM_ (uncurry thunk) bs
        e
{-# INLINE let' #-}

thunkedLet' :: forall sig sigs sigl m a. (Let sig sigl a, EffectCons m sig sigs sigl Id) => [(VarIndex, Ptr)] -> m a -> m a
thunkedLet' bs e = logCall >> do
    redirect @a bs
    e
{-# INLINE thunkedLet' #-}