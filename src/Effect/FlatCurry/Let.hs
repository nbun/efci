{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Effect.FlatCurry.Let where

import Curry.FlatCurry.Type (VarIndex)
import qualified Data.IntMap as IntMap
import Effect.General.Memoization
import Effect.General.State
import Free
import Signature

data LocalBindings

instance Identify LocalBindings where
  identify = "LocalBindings"

type Ptrs = IntMap.IntMap Ptr

type Let sig sigl a =
  (StateF LocalBindings Ptrs :<: sig, Renaming :<: sig, Thunking a :<<<<: sigl)

lvar
  :: (Let sig sigl a, EffectMonad m sig sigs sigl Id)
  => Scope
  -> VarIndex
  -> m a
lvar scope i = do
  s <- get @LocalBindings
  i' <- lookupRenaming scope i
  case IntMap.lookup i' s of
    Nothing -> error $ "Unbound variable " ++ show i
    Just ptr -> force ptr
{-# INLINE lvar #-}

let'
  :: (EffectMonad m sig sigs sigl Id, Let sig sigl a)
  => Scope
  -> [(VarIndex, m a)]
  -> m a
  -> m a
let' scope bs e = do
  let (vs, ps) = unzip bs
  ptrs <- mapM thunk ps
  letThunked scope (zip vs ptrs) e
{-# INLINE let' #-}

letThunked
  :: (EffectMonad m sig sigs sigl Id, Let sig sigl a)
  => Scope
  -> [(VarIndex, Ptr)]
  -> m a
  -> m a
letThunked scope bs e = do
  let (vs, ptrs) = unzip bs
  vs' <- rename scope vs
  s <- get @LocalBindings
  put @LocalBindings (foldr (uncurry IntMap.insert) s (zip vs' ptrs))
  e
{-# INLINE letThunked #-}