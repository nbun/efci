{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Pipeline where

import Curry.FlatCurry (Literal (..), QName, VarIndex)
import qualified Data.IntMap as IntMap
import Data.List (intercalate)
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Function
import Effect.FlatCurry.IO (runIO)
import Effect.FlatCurry.Let (LocalBindings)
import Effect.General.Error (Error (..), runError)
import Effect.General.Memoization
import Effect.General.ND (runND)
import Effect.General.Reader
import Effect.General.State
import Free
import Signature
import Transformation.FCY2AE
import Type (AEProg)

runCurryEffects
  :: (Show a)
  => [AEProg (Prog (CurryEffects a) a)]
  -> Prog (CurryEffects a) a
  -> IO (Error [Value (Closure a)])
runCurryEffects ps =
  runIO
    . runError
    . runND
    . runState @CStore IntMap.empty
    . runState @FunctionState []
    . runState @Rename ((0, 0), [])
    . runState @LocalBindings IntMap.empty
    . runLazy (0, IntMap.empty)
    . runCons
    . runPartial
    . runReader ps
    . f

f
  :: Prog (CurryEffects v) a
  -> Prog (Sig (AEF (CurryEffects v) v) SEffects (LEffects v) Id) a
f (Return x) = Return x
f (Call op) = Call $
  case op of
    A (Algebraic op) -> A (Algebraic (f <$> unwrap op))
    S (Enter op) -> S (Enter (fmap f . f <$> op))
    L (Node op l st k) -> L (Node op l (\c lv -> f $ st c lv) (f . k))
 where
  unwrap (AEffects x) = x


data Result
  = RLit Literal
  | RCons QName [Result]
  | Unevaluated
  | RClosure QName CombType
  | RError String
  | RFree VarIndex
  | ROther String
  deriving (Show, Eq)

declutter :: (Show a) => Error [Value (Closure a)] -> [Result]
declutter (Error s) = [RError s]
declutter (EOther xs) = map declutterHNF xs

declutterHNF :: (Show a) => Value (Closure a) -> Result
declutterHNF (Cons qn args) = RCons qn (map declutterHNF args)
declutterHNF (HNF qn ptrs) = RCons qn (replicate (length ptrs) Unevaluated)
declutterHNF (Lit l) = RLit l
declutterHNF (Free i) = RFree i
declutterHNF (ValOther c) = case c of
  Closure qn ct _ -> RClosure qn ct
  Other x -> ROther (show x)

class Pretty a where
  pretty :: a -> String

instance Pretty Result where
  pretty r@(RCons ("Prelude", ":") _) = prettyList r
  pretty (RCons ("Prelude", "(,)") [x, y]) =
    "(" ++ pretty x ++ ", " ++ pretty y ++ ")"
  pretty (RCons ("Prelude", "(,,)") [x, y, z]) =
    "(" ++ pretty x ++ ", " ++ pretty y ++ ", " ++ pretty z ++ ")"
  pretty (RCons qn []) = snd qn
  pretty (RCons qn vs) = parOnce $ snd qn ++ " " ++ unwords (map pretty vs)
  pretty (RLit (Intc i)) = show i
  pretty (RLit (Charc c)) = show c
  pretty (RLit (Floatc f)) = show f
  pretty Unevaluated = "Unevaluated"
  pretty (RClosure qn ct) =
    snd qn ++ " " ++ unwords (replicate (missingArgs ct) "_")
  pretty (RError s) = "Error: " ++ s
  pretty (RFree i) = "_" ++ show i
  pretty (ROther s) = s

prettyList :: Result -> String
prettyList r = "[" ++ intercalate ", " (prettyList' r) ++ "]"
 where
  prettyList' (RCons ("Prelude", ":") [x, y]) = pretty x : prettyList' y
  prettyList' (RCons ("Prelude", "[]") []) = []

parOnce :: String -> String
parOnce "" = ""
parOnce s@('(' : _) = s
parOnce s = '(' : s ++ ")"
