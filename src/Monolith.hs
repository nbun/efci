{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Monolith (runMonolithic) where

import Curry.FlatCurry.Annotated.Type
import Effect.FlatCurry.Constructor (Value(..))
import qualified Effect.FlatCurry.Function as FCF
import Effect.FlatCurry.Function (Closure(..))


-- A Thunk is an unevaluated expression with its environment (not cyclic)
data Thunk = Thunk [(VarIndex, Thunk)] (AExpr TypeExpr)

-- Extend Value to allow constructor arguments to be thunks
data LValue = LCons QName [Thunk] | LLit Literal | LClosure QName [Thunk]

runMonolithic :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> [Value (Closure ())]
runMonolithic progs fdecl =
  let funs = concat [fs | AProg _ _ _ fs _ <- progs]
      expr = case fdecl of
        AFunc _ _ _ _ (ARule _ _ e) -> e
        _ -> error "External function not supported"
      env0 = []
      lvals = leval funs env0 expr
  in concatMap (fromLValue funs) lvals

leval :: [AFuncDecl TypeExpr] -> [(VarIndex, Thunk)] -> AExpr TypeExpr -> [LValue]
leval funs env ex = case ex of
  AVar _ v ->
    case lookup v env of
      Just th -> lwhnf funs th
      Nothing -> error $ "Unbound variable: " ++ show v
  ALit _ l -> [LLit l]
  AComb _ ctype (qn, _) args ->
    let argThunks = map (\a -> Thunk env a) args in
    case ctype of
      ConsCall -> [LCons qn argThunks]
      ConsPartCall _ -> [LCons qn argThunks]
      FuncCall -> lapplyFun funs qn argThunks
      Curry.FlatCurry.Annotated.Type.FuncPartCall _ -> lapplyFun funs qn argThunks
  ALet _ bs e ->
    let env' = [(v, Thunk env be) | ((v, _), be) <- bs] ++ env in
    leval funs env' e
  AFree _ _ e -> leval funs env e
  AOr _ e1 e2 -> leval funs env e1 ++ leval funs env e2
  ACase _ _ e brs ->
    let vs = leval funs env e in
    concatMap (lmatchBranches funs env brs) vs
  ATyped _ e _ -> leval funs env e

lwhnf :: [AFuncDecl TypeExpr] -> Thunk -> [LValue]
lwhnf funs (Thunk env ex) = leval funs env ex

lapplyFun :: [AFuncDecl TypeExpr] -> QName -> [Thunk] -> [LValue]
lapplyFun funs qn args =
  case [f | f@(AFunc qn' ar _ _ _) <- funs, qn' == qn, ar == length args] of
    (AFunc _ _ _ _ (ARule _ params body) : _) ->
      let env' = zip (map fst params) args
      in leval funs env' body
    _ -> [LClosure qn args]

lmatchBranches :: [AFuncDecl TypeExpr] -> [(VarIndex, Thunk)] -> [ABranchExpr TypeExpr] -> LValue -> [LValue]
lmatchBranches _ _ [] _ = []
lmatchBranches funs env (ABranch pat be : bs) v =
  case lmatchPat pat v of
    Just env' -> leval funs (env' ++ env) be
    Nothing   -> lmatchBranches funs env bs v

lmatchPat :: APattern TypeExpr -> LValue -> Maybe [(VarIndex, Thunk)]
lmatchPat (ALPattern _ l) (LLit l') | l == l' = Just []
lmatchPat (APattern _ (qn, _) vars) (LCons qn' args)
  | qn == qn' && length vars == length args = Just (zip (map fst vars) args)
  | otherwise = Nothing
lmatchPat _ _ = Nothing

fromLValue :: [AFuncDecl TypeExpr] -> LValue -> [Value (Closure ())]
fromLValue _ (LLit l) = [Lit l]
fromLValue funs (LCons qn thunks) =
  let argVals = map (\th -> fromLValue funs =<< lwhnf funs th) thunks
  in [Effect.FlatCurry.Constructor.Cons qn vs | vs <- sequence argVals]
fromLValue _ (LClosure qn thunks) = [ValOther (Closure qn (FCF.FuncPartCall (length thunks)) [])]
