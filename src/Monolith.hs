{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Monolith where

import Control.Monad.State (StateT, evalStateT, get, put)
import qualified Control.Monad.State.Class
import Curry.FlatCurry.Annotated.Type
import qualified Data.Map as Map
import Effect.FlatCurry.Constructor (Value (..))
import Effect.FlatCurry.Function (Closure (..))
import Effect.General.Error (Error (..))
import Effect.General.Memoization (Ptr)
import Effect.General.State (Constraints, Scope, TraceInfo)
import Data.Maybe (mapMaybe)

-- IO ([TraceInfo], Error [(Constraints, Value (Closure a))])

-- data Result = Error String | Results [Result']
-- data Result' =

type Result = ([TraceInfo], Error [(Constraints, Value (Closure ()))])

data State = State {memo :: Map.Map (Scope, Int) (Either (AExpr TypeExpr) Result), currentScope :: Scope}

initial :: State
initial = State{memo = Map.empty, currentScope = 0}

runMonolithic :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> IO Result
runMonolithic ps (AFunc _ _ _ _ (ARule _ _ e)) = evalStateT (execute ps e) initial

execute :: [AProg TypeExpr] -> AExpr TypeExpr -> StateT State IO Result
execute ps expr = case expr of
    ALit _ l -> return $ ([], EOther [(Map.empty, Lit l)])
    AVar _ i -> do
        s <- get
        case Map.lookup (currentScope s, i) (memo s) of
            Nothing -> error "Variable not found"
            Just x -> case x of
                Left e -> execute ps e
                Right r -> return r
    ALet _ bs e -> do
        s <- get
        let (vs, es) = unzip bs
        let' s (map fst vs) es
        execute ps e
    AComb _ ct qn args -> case ct of
        FuncCall -> do
            s <- get
            let fd = findModule ps (fst qn)
            let' s (fdclVars fd) args
            execute ps (fdclBody fd)
        _ -> error "Comb type not supported"
    AOr _ e1 e2 -> do
        r1 <- execute ps e1
        r2 <- execute ps e2
        return $ case (r1, r2) of
            ((_, Error s), _) -> ([], Error s)
            (_, (_, Error s)) -> ([], Error s)
            ((_, EOther xs), (_, EOther ys)) -> ([], EOther (xs ++ ys))
    ACase _ _ e alts -> do
        r <- execute ps e
        case r of
            (_, Error s) -> return ([], Error s)
            (_, EOther xs) -> do
                case mapMaybe (undefined (snd $ head xs)) alts of
                  [] -> return ([], EOther [])
                --   [x] -> return x
                --   xs -> choose xs
    ATyped _ e _ -> execute ps e

let' :: (Control.Monad.State.Class.MonadState State m) => State -> [VarIndex] -> [AExpr TypeExpr] -> m ()
let' s vs es = put $ s{memo = Map.union (Map.fromList (zip (map (currentScope s,) vs) (map Left es))) (memo s)}

-- match :: Value a -> ABranchExpr TypeExpr -> Maybe Result
-- match (HNF qn args) (ABranch (APattern _ (pqn, _) argVars) e)
--     | pqn == qn = Just $ do
--         s <- get
--         let' s (map fst argVars) args
--         execute ps e
--     | otherwise = Nothing
-- match (Lit l) (ABranch (ALPattern _ lp) e)
--     | l == lp = Just e
--     | otherwise = Nothing
-- match (Free i) pat = Just $ do
--     case pat of
--         (APattern _ (pqn, _) argVars, e) -> do
--             vs <- freshNames (length argVars)
--             let fvs = map (fvar scope) vs
--             modify @CStore (addC i (ConsC pqn (map (scope,) vs)))
--             let' scope (zip (map fst argVars) fvs) e
--         (ALPattern _ lp, e) -> do
--             modify @CStore (addC i (LitC lp))
--             e
match v ps =
    error $
        "Pattern match not implemented for " ++ show v ++ show (fst ps)

findModule :: [AProg a] -> QName -> AFuncDecl a
findModule ps qn@(mod, _) = case res of
    Just fdecl -> fdecl
    Nothing -> error $ "Function declaration " ++ show qn ++ " not found"
  where
    res =
        foldr
            ( \(AProg name _ _ fdecls _) acc ->
                if name == mod
                    then findFuncDecl fdecls qn
                    else acc
            )
            Nothing
            ps

findFuncDecl :: [AFuncDecl a] -> QName -> Maybe (AFuncDecl a)
findFuncDecl fd qn = foldr (\fdecl acc -> if qn == funcName fdecl then Just fdecl else acc) Nothing fd
  where
    funcName (AFunc qn _ _ _ _) = qn

fdclBody :: AFuncDecl a -> AExpr a
fdclBody (AFunc _ _ _ _ (ARule _ _ a)) = a

fdclVars :: AFuncDecl a -> [VarIndex]
fdclVars (AFunc _ _ _ _ (ARule _ vs _)) = map fst vs