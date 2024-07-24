{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Effect.FlatCurry.Free where

import Curry.FlatCurry.Type (
  TypeExpr (..),
  VarIndex,
 )
import Debug (ctrace)
import Effect.FlatCurry.Function (
  CombType (..),
  FunctionState,
  Functions,
  fun,
  partial,
 )
import Effect.FlatCurry.Let (Let, let')
import Effect.General.Memoization (Thunking)
import Effect.General.State
import Free
import Signature

free
  :: (Functions sig sigs sigl a, Let sig sigl a)
  => Scope
  -> [(VarIndex, TypeExpr)]
  -> Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) (Prog (Sig sig sigs sigl Id) a)
free scope is p = ctrace ("free: " ++ show (map snd is)) $
  do
    let (vs, ts) = unzip is
    es <- mapM (ndGen False) ts
    return $ let' scope (zip vs es) p

ndGen
  :: (Functions sig sigs sigl a, Thunking a :<<<<: sigl)
  => Bool
  -> TypeExpr
  -> Prog (Sig sig sigs sigl Id) (Prog (Sig sig sigs sigl Id) a)
ndGen useDict (TCons (mod, dt) args) = ctrace ("ndGen: " ++ dt) $
  do
    args' <- mapM (ndGen True) args
    let qual =
          if opType dt
            then ""
            else mod ++ "."
    if useDict
      then
        return $
          partial
            (mod, "_inst#" ++ mod ++ ".Data#" ++ qual ++ dt)
            (FuncPartCall 1)
            args'
      else do
        scope <- newScope
        return $
          fun
            scope
            (mod, "_impl#aValue#Prelude.Data#" ++ qual ++ dt)
            (Left args')
ndGen useDict (ForallType _ t) = ndGen useDict t
ndGen _ (TVar i) = do
  scope <- currentScope
  return $
    do
      dicts <- get @FunctionState
      case lookup (scope, TVar i) dicts of
        Nothing -> undefined
        Just ptr -> do
          scope <- newScope
          fun scope ("Prelude", "aValue") (Right [ptr])
ndGen _ _ = undefined

opType :: String -> Bool
opType "[]" = True
opType "()" = True
opType "(,)" = True
opType "(,,)" = True
opType "(,,,)" = True
opType "(,,,,)" = True
opType "(,,,,,)" = True
opType "(,,,,,,)" = True
opType "(->)" = True
opType _ = False