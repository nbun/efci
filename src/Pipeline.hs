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
import Effect.FlatCurry.IO (runIO, IOC (..), runIOSmart)
import Effect.General.Error (Error (..), runError, ErrorL, EC, runErrorC, runErrorSmart)
import Effect.General.Memoization
import Effect.General.ND (runND, ListL, NDC, runNDC, runNDSmart)
import Effect.General.Reader
import Effect.General.State
import Free
import Signature
import Transformation.FCY2AE
import Type (AEProg)
import Effect.FlatCurry.Declarations
import qualified Data.Map as Map
import Effect.FlatCurry.Let
import GHC.Types.Unique.Supply (mkSplitUniqSupply)
import Effect.General.Delay

runCurryEffects :: (Show a, Vars a)
                => [AEProg (Prog (CurryEffects a) a)]
                -> Prog (CurryEffects a) a
                -> IO ([TraceInfo], Error [(Constraints, Value (Closure a))])
runCurryEffects ps e = mkSplitUniqSupply 'a' >>= \sup -> pipeline sup e'
  where
    e' = initDecls ps >> e
    pipeline sup = runIO
      . (\x -> hState @Trace x ([] :: [TraceInfo]))
      . runError
      . runND
      . (\x -> hState @CStore x Map.empty)
      . runState @Rename ((0, 0, [], sup, []))
      . runState @LocalBindings Map.empty
      . runLazy
      . runDelay
      . runCons
      . runPartial
      . runDecl []

runSmartCurryEffects :: (Show a, Vars a)
                => [AEProg (SmartProg (CurryEffects a) a)]
                -> SmartProg (CurryEffects a) a
                -> IO ([TraceInfo], Error [(Constraints, Value (Closure a))])
runSmartCurryEffects ps e = mkSplitUniqSupply 'a' >>= \sup -> pipeline sup e'
  where
    e' = initDecls ps >> e
    pipeline sup = runIOSmart
      . (\x -> hStateSmart @Trace x ([] :: [TraceInfo]))
      . runErrorSmart
      . runNDSmart
      . (\x -> hStateSmart @CStore x Map.empty)
      . runStateSmart @Rename ((0, 0, [], sup, []))
      . runStateSmart @LocalBindings Map.empty
      . runLazySmart
      . runDelaySmart
      . runConsSmart
      . runPartialSmart
      . runDeclSmart []

declutter :: Show a => ([TraceInfo], Error [(Constraints, Value (Closure a))]) -> ([TraceInfo], [Result])
declutter (ti, Error s) = (ti, [RError s])
declutter (ti, EOther xs) = (ti, map addBindings xs)
  where
    addBindings (bs, v)
      | Map.null bs || all (\(_,i) -> i > 999) (Map.keys bs) = declutterHNF v
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
            | RFree (Scope, VarIndex)
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
    "{" ++ intercalate ", " (map pretty (Map.toList cs)) ++ "} " ++ pretty r
  pretty (ROther s) = s

instance Pretty ((Scope, VarIndex), CValue) where
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
    prettyList' x = [show x]

parOnce :: String -> String
parOnce "" = ""
parOnce s@('(':_) = s
parOnce s = '(':s ++ ")"

type L a = StateL [TraceInfo]
                      (ErrorL
                         (ListL
                            (StateL
                               Constraints
                                  (StateL
                                     (Scope, VarIndex)
                                     (StateL
                                        Ptrs
                                        (StateL
                                           (ThunkStore (ValueL (ClosureL Id)) a)
                                           (ValueL (ClosureL Id))))))))

type Co = (Cod (STC LocalBindings Ptrs
            (Cod (STC Rename (Scope, VarIndex)
                (Cod (STC CStore Constraints
                  (Cod (NDC
                    (Cod (EC
                      (Cod (STC Trace [TraceInfo]
                        (Cod (IOC T2))))))))))))))

type T2 = StateL [TraceInfo] (ErrorL
                         (ListL
                            (StateL
                               Constraints
                                  (StateL
                                     (Scope, VarIndex)
                                     (StateL Ptrs (ValueL (ClosureL Id)))))))

type M a =           Cod
                         (H (Cod
                               (PC
                                  (Cod
                                     (CC
                                        (Cod
                                           (MC
                                              (Cod
                                                 (STC
                                                    LocalBindings
                                                    Ptrs
                                                    (Cod
                                                       (STC
                                                          Rename
                                                          (Scope, VarIndex)
                                                                (Cod
                                                                   (STC
                                                                      CStore
                                                                      Constraints
                                                                      (Cod
                                                                         (NDC
                                                                            (Cod
                                                                               (EC
                                                                                  (Cod
                                                                                    (STC Trace [TraceInfo]
                                                                                      (Cod
                                                                                        (IOC
                                                                                          (L 
                                                                                             a)))))))))))))))
                                              (ValueL (ClosureL Id))
                                              a))))))
                            Id
                            a)

-- {-# SPECIALISE runCurryEffectsC :: [AEProg ((M ()) ())]
--                  -> (M ()) ()
--                  -> IO (Error [(Constraints, Value (Closure ()))]) #-}

runCurryEffectsC :: forall a.
                 (Show a, Vars a)
                 => [AEProg ((M a) a)]
                 -> (M a) a
                 -> IO ([TraceInfo], Error [(Constraints, Value (Closure a))])
runCurryEffectsC ps e = unIOC (pipeline e' ) -- :: IOC (L Co a) ([TraceInfo], Error [(Constraints, Value (Closure a))]))
  where
    e' = initDecls ps >> e
    pipeline = finish
      . runStateC @Trace []
      . runErrorC
      . runNDC
      . runStateC @CStore Map.empty
      . runStateC' @Rename ((0, 0))
      . runStateC' @LocalBindings Map.empty
      . runLazyC
      . runConsC
      . runPartialC
      . runDeclC []
    {-# INLINE pipeline #-}