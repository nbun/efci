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

import Effect.General.Memoization
import Effect.General.State
import Signature
import Type

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
    :: forall m sig sigs sigl a. (EffectCons m sig sigs sigl Id, Let sig sigl a)
    => [Ptr]
    -> Args m a
    -> m a
    -> m a
let' vs args e = logCall >> case args of
  Progs ps -> mapM_ (uncurry thunk) (zip vs ps) >> e
  Thunks ptrs -> mapM_ (redirect @a) (zip vs ptrs) >> e
{-# INLINE let' #-}