module Monolith (runMonolithic) where

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

import Curry.FlatCurry.Annotated.Type
import Effect.FlatCurry.Constructor (Value(..))
import Effect.FlatCurry.Function (Closure(..), CombType(FuncPartCall))
import Effect.General.Error (Error(EOther))

runMonolithic :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> [Value (Closure ())]
runMonolithic progs fdecl = vals
	where
		funs = concat [fs | AProg _ _ _ fs _ <- progs]
		expr = case fdecl of
			AFunc _ _ _ _ (ARule _ _ e) -> e
			_ -> error "External function not supported"
		env0 = []
		-- Evaluate the entry function body
		eval :: [(VarIndex, Value (Closure ()))] -> AExpr TypeExpr -> [Value (Closure ())]
		eval env ex = case ex of
			AVar _ v ->
				case lookup v env of
					Just v' -> [v']
					Nothing -> error $ "Unbound variable: " ++ show v
			ALit _ l -> [Lit l]
			AComb _ ctype (qn, _) args ->
				let
					argVals = map (eval env) args
					argVals' = map getSingleton argVals
				in case ctype of
					ConsCall -> [Effect.FlatCurry.Constructor.Cons qn argVals']
					ConsPartCall _ -> [Effect.FlatCurry.Constructor.Cons qn argVals']
					FuncCall -> applyFun qn argVals'
					Curry.FlatCurry.Annotated.Type.FuncPartCall _ -> applyFun qn argVals'
			ALet _ bs e ->
				let env' = [(v, getSingleton (eval env be)) | ((v, _), be) <- bs] ++ env
				in eval env' e
			AFree _ _ e -> eval env e
			AOr _ e1 e2 -> eval env e1 ++ eval env e2
			ACase _ _ e brs ->
				let vs = eval env e
				in concatMap (matchBranches env brs) vs
			ATyped _ e _ -> eval env e
		getSingleton [x] = x
		getSingleton [] = error "Empty list in eval"
		getSingleton _  = error "Non-singleton list in eval"

		applyFun :: QName -> [Value (Closure ())] -> [Value (Closure ())]
		applyFun qn args =
			case [f | f@(AFunc qn' ar _ _ r) <- funs, qn' == qn, ar == length args] of
				(AFunc _ _ _ _ (ARule _ params body) : _) ->
					let env' = zip (map fst params) args
					in eval env' body
				_ -> [ValOther (Closure qn (Effect.FlatCurry.Function.FuncPartCall (length args)) [])]

		matchBranches :: [(VarIndex, Value (Closure ()))] -> [ABranchExpr TypeExpr] -> Value (Closure ()) -> [Value (Closure ())]
		matchBranches _ [] _ = []
		matchBranches env (ABranch pat be : bs) v =
			case matchPat pat v of
				Just env' -> eval (env' ++ env) be
				Nothing   -> matchBranches env bs v

		matchPat :: APattern TypeExpr -> Value (Closure ()) -> Maybe [(VarIndex, Value (Closure ()))]
		matchPat (ALPattern _ l) (Lit l') | l == l' = Just []
		matchPat (APattern _ (qn, _) vars) (Effect.FlatCurry.Constructor.Cons qn' args)
			| qn == qn' && length vars == length args = Just (zip (map fst vars) args)
			| otherwise = Nothing
		matchPat _ _ = Nothing

		vals = eval env0 expr
		