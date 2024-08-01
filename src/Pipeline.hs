{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Pipeline where

import Curry.FlatCurry (Literal (..), QName, VarIndex, TypeExpr)
import qualified Data.IntMap as IntMap
import Data.List (intercalate)
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Function
import Effect.FlatCurry.IO (runIO, IOC (..))
import Effect.FlatCurry.Let (LocalBindings)
import Effect.General.Error (Error (..), runError, ErrorL, EC, runErrorC)
import Effect.General.Memoization
import Effect.General.ND (runND, ListL, NDC, runNDC)
import Effect.General.Reader
import Effect.General.State
import Free
import Signature
import Transformation.FCY2AE
import Type (AEProg)
import Effect.FlatCurry.Declarations

runCurryEffects :: (Show a)
                => [AEProg (Prog (CurryEffects a) a)]
                -> Prog (CurryEffects a) a
                -> IO (Error [(Constraints, Value (Closure a))])
runCurryEffects ps e = pipeline e'
  where
    e' = initDecls ps >> e 
    pipeline = runIO
      . runError
      . runND
      . (\x -> hState @CStore x IntMap.empty)
      . runState @FunctionState []
      . runState @Rename ((0, 0), [])
      . runState @LocalBindings IntMap.empty
      . runLazy (0, IntMap.empty)
      . runCons
      . runPartial
      . runDecl []

declutter :: Show a => Error [(Constraints, Value (Closure a))] -> [Result]
declutter (Error s) = [RError s]
declutter (EOther xs) = map addBindings xs
  where
    addBindings (bs, v)
      | IntMap.null bs || all (> 999) (IntMap.keys bs) = declutterHNF v
      | otherwise = RBindings bs (declutterHNF v)

declutterHNF :: Show a => Value (Closure a) -> Result
declutterHNF (Cons qn args) = RCons qn (map declutterHNF args)
declutterHNF (HNF qn ptrs) = RCons qn (replicate (length ptrs) Unevaluated)
declutterHNF (Lit l) = RLit l
declutterHNF (Free i) = RFree i
declutterHNF (ValOther c) = case c of
  Closure qn ct _ -> RClosure qn ct
  Other x         -> ROther (show x)

data Result = RLit Literal
            | RCons QName [Result]
            | Unevaluated
            | RClosure QName CombType
            | RError String
            | RFree VarIndex
            | ROther String
            | RBindings Constraints Result
  deriving (Show, Eq)

withoutBindings :: Result -> Result
withoutBindings (RBindings _ r) = withoutBindings r
withoutBindings r = r

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
  pretty (RFree i) = "_" ++ show i
  pretty Unevaluated = "Unevaluated"
  pretty (RClosure qn ct) =
    snd qn ++ " " ++ unwords (replicate (missingArgs ct) "_")
  pretty (RError s) = "Error: " ++ s
  pretty (RBindings cs r) =
    "{" ++ intercalate ", " (map pretty (IntMap.toList cs)) ++ "} " ++ pretty r
  pretty (ROther s) = s

instance Pretty (VarIndex, CValue) where
  pretty (i, LitC l) = '_':show i ++ " -> " ++ show l
  pretty (i, VarC j) = '_':show i ++ " -> " ++ show j
  pretty (i, ConsC qn []) = '_':show i ++ " -> " ++ snd qn
  pretty (i, ConsC qn vs) = '_'
    :show i ++ " -> " ++ parOnce (snd qn ++ " " ++ unwords (map show vs))

prettyList :: Result -> String
prettyList r = "[" ++ intercalate ", " (prettyList' r) ++ "]"
  where
    prettyList' (RCons ("Prelude", ":") [x, y]) = pretty x:prettyList' y
    prettyList' (RCons ("Prelude", "[]") []) = []

parOnce :: String -> String
parOnce "" = ""
parOnce s@('(':_) = s
parOnce s = '(':s ++ ")"

type L c a = ErrorL
                         (ListL
                            (StateL
                               Constraints
                               (StateL
                                  [((Scope, TypeExpr), Ptr)]
                                  (StateL
                                     ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)])
                                     (StateL
                                        (IntMap.IntMap Ptr)
                                        (StateL
                                           (ThunkStore c (ValueL (ClosureL Id)) a)
                                           (ValueL (ClosureL Id))))))))

type Co = (Cod (STC LocalBindings (IntMap.IntMap Ptr)
            (Cod (STC Rename ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)])
              (Cod (STC FunctionState [((Scope, TypeExpr), Ptr)]
                (Cod (STC CStore Constraints
                  (Cod (NDC
                    (Cod (EC
                      (Cod (IOC T2))))))))))))))

type T2 = ErrorL
                         (ListL
                            (StateL
                               Constraints
                               (StateL
                                  [((Scope, TypeExpr), Ptr)]
                                  (StateL
                                     ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)])
                                     (StateL (IntMap.IntMap Ptr) (ValueL (ClosureL Id)))))))

type M a = Cod
                         (H (Cod
                               (PC
                                  (Cod
                                     (CC
                                        (Cod
                                           (MC
                                              (Cod
                                                 (STC
                                                    LocalBindings
                                                    (IntMap.IntMap Ptr)
                                                    (Cod
                                                       (STC
                                                          Rename
                                                          ((Scope, VarIndex),
                                                           [((Scope, VarIndex), VarIndex)])
                                                          (Cod
                                                             (STC
                                                                FunctionState
                                                                [((Scope, TypeExpr), Ptr)]
                                                                (Cod
                                                                   (STC
                                                                      CStore
                                                                      Constraints
                                                                      (Cod
                                                                         (NDC
                                                                            (Cod
                                                                               (EC
                                                                                  (Cod
                                                                                     (IOC
                                                                                        (L Co
                                                                                           a)))))))))))))))
                                              (ValueL (ClosureL Id))
                                              a))))))
                            Id
                            a)

runCurryEffectsC :: forall a.
                 (Show a)
                 => [AEProg ((M a) a)]
                 -> (M a) a
                 -> IO (Error [(Constraints, Value (Closure a))])
runCurryEffectsC ps e = unIOC (pipeline e' :: IOC (L Co a) (Error [(Constraints, Value (Closure a))]))
  where
    e' = initDecls ps >> e
    pipeline = finish
      . runErrorC
      . runNDC
      . runStateC @CStore IntMap.empty
      . runStateC' @FunctionState []
      . runStateC' @Rename ((0, 0), [])
      . runStateC' @LocalBindings IntMap.empty
      . runLazyC (0, IntMap.empty)
      . runConsC
      . runPartialC
      . runDeclC []
    {-# INLINE pipeline #-}