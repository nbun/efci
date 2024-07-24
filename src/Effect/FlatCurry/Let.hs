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
  :: (Let sig sigl a, Functor sig, Functor sigs)
  => Scope
  -> VarIndex
  -> Prog (Sig sig sigs sigl Id) a
lvar scope i = do
  s <- get @LocalBindings
  i' <- lookupRenaming scope i
  case IntMap.lookup i' s of
    Nothing -> error $ "Unbound variable " ++ show i
    Just ptr -> force ptr

let'
  :: ( StateF LocalBindings Ptrs :<: sig
     , Thunking a :<<<<: sigl
     , Functor sig
     , Functor sigs
     , Renaming :<: sig
     )
  => Scope
  -> [(VarIndex, Prog (Sig sig sigs sigl Id) a)]
  -> Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
let' scope bs e = do
  let (vs, ps) = unzip bs
  ptrs <- mapM thunk ps
  letThunked scope (zip vs ptrs) e

letThunked
  :: ( StateF LocalBindings Ptrs :<: sig
     , Thunking a :<<<<: sigl
     , Functor sig
     , Functor sigs
     , Renaming :<: sig
     )
  => Scope
  -> [(VarIndex, Ptr)]
  -> Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
letThunked scope bs e = do
  let (vs, ptrs) = unzip bs
  vs' <- rename scope vs
  s <- get @LocalBindings
  put @LocalBindings (foldr (uncurry IntMap.insert) s (zip vs' ptrs))
  e