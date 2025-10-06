{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Monolith (runMonolithic) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, forM_, msum, mzero)
import Control.Monad.State
import Curry.FlatCurry.Annotated.Type
import Data.Map (Map, insert)
import qualified Data.Map as Map
import Effect.FlatCurry.Constructor (Value (..))
import qualified Effect.FlatCurry.Function as FCF
import Effect.FlatCurry.Function (Closure (..))


-- Evaluation plumbing
type Ptr = Int
type Heap = Map Ptr Node
type Env = [(VarIndex, Ptr)]
data EvalState = EvalState {heap :: Heap, nextPtr :: Ptr, output :: String}
type Eval a = StateT EvalState [] a

-- Values on the heap
data Node
  = NCons QName [Ptr]
  | NLit Literal
  | NClosure QName [Ptr]
  | NThunk Env (AExpr TypeExpr)

-- Values returned by evaluation (Weak Head Normal Form)
data LValue
  = LCons QName [Ptr]
  | LLit Literal
  | LClosure QName [Ptr]

runMonolithic :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> IO [(Value (Closure ()))]
runMonolithic progs fdecl = do
  let funs = concat [fs | AProg _ _ _ fs _ <- progs]
      expr = case fdecl of
        AFunc _ _ _ _ (ARule _ _ e) -> e
        _ -> error "External function not supported"
      initialState = EvalState Map.empty 0 ""
      eval_and_convert = do
        v <- leval funs [] expr
        fromLValueM funs v
  let results = runStateT eval_and_convert initialState
  forM_ results $ \(_, s) -> putStr (output s)
  return (map fst results)

-- Main evaluation function
leval :: [AFuncDecl TypeExpr] -> Env -> AExpr TypeExpr -> Eval LValue
leval funs env ex = case ex of
  AVar _ v -> case Prelude.lookup v env of
    Just ptr -> lwhnf funs ptr
    Nothing -> error ("Unbound variable: " ++ show v)
  ALit _ l -> return (LLit l)
  AComb _ ctype (qn, _) args -> do
    argPtrs <- mapM (allocThunk env) args
    case ctype of
      ConsCall -> return (LCons qn argPtrs)
      ConsPartCall _ -> return (LCons qn argPtrs)
      FuncCall -> lapplyFun funs qn argPtrs
      Curry.FlatCurry.Annotated.Type.FuncPartCall _ -> lapplyFun funs qn argPtrs
  ALet _ bs e -> do
    env' <- extendEnv env bs
    leval funs env' e
  AFree _ vs e -> do
    env' <- foldM (\acc (v, ty) -> do
      val <- generateValue ty
      ptr <- alloc (toNode val)
      return ((v, ptr) : acc)
      ) env vs
    leval funs env' e
  AOr _ e1 e2 -> leval funs env e1 <|> leval funs env e2
  ACase _ _ e brs -> do
    ptr <- allocThunk env e
    v <- lwhnf funs ptr
    lmatchBranches funs env brs v
  ATyped _ e _ -> leval funs env e

-- Force evaluation of a node to WHNF
lwhnf :: [AFuncDecl TypeExpr] -> Ptr -> Eval LValue
lwhnf funs ptr = do
  node <- gets ((Map.! ptr) . heap)
  case node of
    NThunk env expr -> do
      v <- leval funs env expr
      modify (updateHeap ptr (toNode v))
      return v
    _ -> return (fromNode node)

-- Function Application
lapplyFun :: [AFuncDecl TypeExpr] -> QName -> [Ptr] -> Eval LValue
lapplyFun funs qn args
  | isPrimitive qn = applyPrimitive funs qn args
  | otherwise = case Prelude.lookup qn [(q, f) | f@(AFunc q _ _ _ _) <- funs] of
    Just (AFunc _ arity _ _ (ARule _ params body)) ->
      if length args < arity
        then return (LClosure qn args)
        else
          let (these, rest) = splitAt arity args
              env' = zip (map fst params) these
           in do
                v <- leval funs env' body
                lapplyLValue funs v rest
    _ -> error ("Function not found: " ++ show qn)

lapplyLValue :: [AFuncDecl TypeExpr] -> LValue -> [Ptr] -> Eval LValue
lapplyLValue _ v [] = return v
lapplyLValue funs (LClosure qn args) more = lapplyFun funs qn (args ++ more)
lapplyLValue _ v _ = return v -- Over-application to a constructor

-- Pattern Matching
lmatchBranches :: [AFuncDecl TypeExpr] -> Env -> [ABranchExpr TypeExpr] -> LValue -> Eval LValue
lmatchBranches funs env branches v = msum (map tryBranch branches)
  where
    tryBranch (ABranch pat body) =
      case lmatchPat pat v of
        Just newBindings ->
          let env' = newBindings ++ env
           in leval funs env' body
        Nothing -> mzero

lmatchPat :: APattern TypeExpr -> LValue -> Maybe Env
lmatchPat (ALPattern _ l) (LLit l') | l == l' = Just []
lmatchPat (APattern _ (qn, _) vars) (LCons qn' args)
  | qn == qn' && length vars == length args = Just (zip (map fst vars) args)
lmatchPat _ _ = Nothing

-- Heap and Environment Helpers
alloc :: Node -> Eval Ptr
alloc node = do
  s <- get
  let ptr = nextPtr s
  put (s {heap = insert ptr node (heap s), nextPtr = ptr + 1})
  return ptr

allocThunk :: Env -> AExpr TypeExpr -> Eval Ptr
allocThunk env expr = alloc (NThunk env expr)

extendEnv :: Env -> [((VarIndex, TypeExpr), AExpr TypeExpr)] -> Eval Env
extendEnv env bindings = do
  newBindings <- forM bindings $ \((v, _), expr) -> do
    ptr <- allocThunk env expr
    return (v, ptr)
  return (newBindings ++ env)

updateHeap :: Ptr -> Node -> EvalState -> EvalState
updateHeap ptr node s = s {heap = insert ptr node (heap s)}

generateValue :: TypeExpr -> Eval LValue
generateValue (TCons ("Prelude", "Bool") []) =
  (return $ LCons ("Prelude", "False") []) <|> (return $ LCons ("Prelude", "True") [])
generateValue ty = error ("Cannot generate values for free variables of type: " ++ show ty)

-- Conversion to final result type
fromLValueM :: [AFuncDecl TypeExpr] -> LValue -> Eval (Value (Closure ()))
fromLValueM _ (LLit l) = return (Lit l)
fromLValueM funs (LCons qn ptrs) = do
    args <- forM ptrs $ \p -> do
        v <- lwhnf funs p
        fromLValueM funs v
    return (Effect.FlatCurry.Constructor.Cons qn args)
fromLValueM _ (LClosure qn ptrs) = return (ValOther (Closure qn (FCF.FuncPartCall (length ptrs)) []))

toNode :: LValue -> Node
toNode (LLit l) = NLit l
toNode (LCons qn ptrs) = NCons qn ptrs
toNode (LClosure qn ptrs) = NClosure qn ptrs

fromNode :: Node -> LValue
fromNode (NLit l) = LLit l
fromNode (NCons qn ptrs) = LCons qn ptrs
fromNode (NClosure qn ptrs) = LClosure qn ptrs
fromNode (NThunk _ _) = error "Cannot convert thunk to LValue directly"

-- Primitive Operations
isPrimitive :: QName -> Bool
isPrimitive (m, n) = m == "Prelude" && n `elem`
  ["plusInt", "minusInt", "timesInt", "divInt", "modInt", "eqInt",
   "ltEqInt", "ltInt", "gtInt", "gtEqInt",
   "and", "or", "not", "apply", "$!", "bindIO", "returnIO", "prim_putChar", "failed", "remInt"]

applyPrimitive :: [AFuncDecl TypeExpr] -> QName -> [Ptr] -> Eval LValue
applyPrimitive funs (_, name) args = case (name, args) of
  ("plusInt", [p1, p2]) -> primIntOp (+) p1 p2
  ("minusInt", [p1, p2]) -> primIntOp (-) p1 p2
  ("timesInt", [p1, p2]) -> primIntOp (*) p1 p2
  ("divInt", [p1, p2]) -> primIntOp div p1 p2
  ("modInt", [p1, p2]) -> primIntOp mod p1 p2
  ("remInt", [p1, p2]) -> primIntOp rem p1 p2
  ("eqInt", [p1, p2]) -> primIntComp (==) p1 p2
  ("ltEqInt", [p1, p2]) -> primIntComp (<=) p1 p2
  ("ltInt", [p1, p2]) -> primIntComp (<) p1 p2
  ("gtInt", [p1, p2]) -> primIntComp (>) p1 p2
  ("gtEqInt", [p1, p2]) -> primIntComp (>=) p1 p2
  ("and", [p1, p2]) -> primAnd p1 p2
  ("or", [p1, p2]) -> primOr p1 p2
  ("not", [p1]) -> primNot p1
  ("apply", [f, x]) -> do
    lf <- lwhnf funs f
    lapplyLValue funs lf [x]
  ("$!", [f, x]) -> do
    lf <- lwhnf funs f
    _ <- lwhnf funs x
    lapplyLValue funs lf [x]
  ("returnIO", [p]) -> lwhnf funs p
  ("bindIO", [m, f]) -> do
    v <- lwhnf funs m
    lapplyLValue funs v [f]
  ("prim_putChar", [p]) -> do
    LLit (Charc c) <- lwhnf funs p
    modify (\s -> s { output = output s ++ [c] })
    return (LCons ("Prelude", "()") [])
  ("failed", _) -> mzero
  _ -> error ("Unknown or unsaturated primitive: " ++ name)
  where
    primAnd p1 p2 = do
      v1 <- lwhnf funs p1
      case v1 of
        LCons ("Prelude", "False") [] -> return $ LCons ("Prelude", "False") []
        LCons ("Prelude", "True") [] -> lwhnf funs p2
        _ -> error "Type error in primitive 'and'"
    primOr p1 p2 = do
      v1 <- lwhnf funs p1
      case v1 of
        LCons ("Prelude", "True") [] -> return $ LCons ("Prelude", "True") []
        LCons ("Prelude", "False") [] -> lwhnf funs p2
        _ -> error "Type error in primitive 'or'"
    primNot p1 = do
      v1 <- lwhnf funs p1
      case v1 of
        LCons ("Prelude", "True") [] -> return $ LCons ("Prelude", "False") []
        LCons ("Prelude", "False") [] -> return $ LCons ("Prelude", "True") []
        _ -> error "Type error in primitive 'not'"
    primIntOp op p1 p2 = do
      LLit (Intc i1) <- lwhnf funs p1
      LLit (Intc i2) <- lwhnf funs p2
      return (LLit (Intc (i1 `op` i2)))
    primIntComp op p1 p2 = do
      LLit (Intc i1) <- lwhnf funs p1
      LLit (Intc i2) <- lwhnf funs p2
      return $ LCons ("Prelude", if i1 `op` i2 then "True" else "False") []
