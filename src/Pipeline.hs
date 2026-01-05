{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Pipeline (
    Result (..),
    pretty,
    runCurryEffects,
    runCurryEffectsC,
    runSmartCurryEffects,
    declutter,
    withoutBindings,
) where

import Curry.FlatCurry (Literal (..), QName)
import Data.List (intercalate)
import qualified Data.Map as Map
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Declarations
import Effect.FlatCurry.Function
import Effect.FlatCurry.IO (IOC (..), runIO, runIOSmart)
import Effect.General.Error (EC, Error (..), ErrorL, runError, runErrorC, runErrorSmart)
import Effect.General.Memoization
import Effect.General.ND (ListL, NDC, runND, runNDC, runNDSmart)
import Effect.General.State
import Free
import GHC.Plugins (splitUniqSupply)
import GHC.Types.Unique.Supply (mkSplitUniqSupply)
import Signature (Id)
import Transformation.FCY2AE
import Type (AEProg, Ptr (..))
import Data.Char (chr)

runCurryEffects
    :: (Show a)
    => [AEProg (Prog (CurryEffects a) a)]
    -> Prog (CurryEffects a) a
    -> IO ([TraceInfo], Error [(Constraints, Value (Closure a))])
runCurryEffects ps e = do
    sup <- mkSplitUniqSupply 'a'
    let (sup1, sup2) = splitUniqSupply sup
        pipeline =
            runIO
                . (\x -> hState @Trace x ([] :: [TraceInfo]))
                . runError
                . runND
                . (\x -> hState @CStore x Map.empty)
                . runState @Rename (initRenaming sup1)
                . runLazy sup2
                . runCons
                . runPartial
                . runDecl (Progs [])
    pipeline (initDecls ps >> e)

runSmartCurryEffects
    :: [AEProg (SmartProg (CurryEffects ()) ())]
    -> SmartProg (CurryEffects ()) ()
    -> IO ([TraceInfo], Error [(Constraints, Value (Closure ()))])
runSmartCurryEffects ps e = do
    sup <- mkSplitUniqSupply (chr 0)
    let (sup1, sup2) = splitUniqSupply sup
        pipeline =
            runIOSmart
                . (\x -> hStateSmart @Trace x ([] :: [TraceInfo]))
                . runErrorSmart
                . runNDSmart
                . (\x -> hStateSmart @CStore x Map.empty)
                . runStateSmart @Rename (initRenaming sup1)
                . runLazySmart sup2
                . runConsSmart
                . runPartialSmart
                . runDeclSmart (Progs [])
    pipeline (initDecls ps >> e)

declutter :: (Show a) => ([TraceInfo], Error [(Constraints, Value (Closure a))]) -> ([TraceInfo], [Result])
declutter (ti, Error s) = (ti, [RError s])
declutter (ti, EOther xs) = (ti, map addBindings xs)
  where
    addBindings (bs, v)
        | Map.null bs || all (\(Ptr i _) -> i > 999) (Map.keys bs) = declutterHNF v
        | otherwise = RBindings bs (declutterHNF v)

declutterHNF :: (Show a) => Value (Closure a) -> Result
declutterHNF (NF qn args) = RCons qn (map declutterHNF args)
declutterHNF (HNF qn ptrs) = RCons qn (replicate (length ptrs) Unevaluated)
declutterHNF (Lit l) = RLit l
declutterHNF (Free i) = RFree i
declutterHNF (ValOther c) = case c of
    Closure qn ct args -> RClosure qn ct (length args)
    Lambda _ _ -> Unevaluated
    Effect.FlatCurry.Function.External _ -> Unevaluated
    Other x -> ROther (show x)

data Result
    = RLit Literal
    | RCons QName [Result]
    | Unevaluated
    | RClosure QName CombType Int
    | RError String
    | RFree Ptr
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
    pretty (RClosure qn ct argc) =
        snd qn ++ " " ++ unwords (replicate argc "_") ++ (if argc == 0 then "" else " ") ++ unwords (replicate (missingArgs ct) "?")
    pretty (RError s) = "Error: " ++ s
    pretty (RBindings cs r) =
        "{" ++ intercalate ", " (map pretty (Map.toList cs)) ++ "} " ++ pretty r
    pretty (ROther s) = s

instance Pretty (Ptr, CValue) where
    pretty (i, LitC l) = '_' : show i ++ " -> " ++ show l
    pretty (i, VarC j) = '_' : show i ++ " -> " ++ show j
    pretty (i, ConsC qn []) = '_' : show i ++ " -> " ++ snd qn
    pretty (i, ConsC qn vs) =
        '_'
            : show i
            ++ " -> "
            ++ parOnce (snd qn ++ " " ++ unwords (map show vs))

prettyList :: Result -> String
prettyList r = "[" ++ intercalate ", " (prettyList' r) ++ "]"
  where
    prettyList' (RCons ("Prelude", ":") [x, y]) = pretty x : prettyList' y
    prettyList' (RCons ("Prelude", "[]") []) = []
    prettyList' x = [show x]

parOnce :: String -> String
parOnce "" = ""
parOnce s@('(' : _) = s
parOnce s = '(' : s ++ ")"

type L a =
    StateL
        [TraceInfo]
        ( ErrorL
            ( ListL
                ( StateL
                    Constraints
                    ( StateL
                        RState
                        ( StateL
                            (ThunkStore (ValueL (ClosureL Id)) a)
                            (ValueL (ClosureL Id))
                        )
                    )
                )
            )
        )

type M a =
    Cod
        ( H (Progs Id a (Cod
                         (PC
                            (Cod
                              (CC
                                  (Cod
                                     (MC
                                        (ValueL (ClosureL Id))
                                        a
                                        (Cod
                                           (STC
                                              Rename
                                                 RState
                                              (Cod
                                                 (STC
                                                    CStore
                                                    (Map.Map Ptr CValue)
                                                    (Cod
                                                       (NDC
                                                          (Cod
                                                             (EC
                                                                (Cod
                                                                   (STC
                                                                      Trace
                                            [TraceInfo]
                                                                      (Cod
                                                                         (IOC
                                                                            (L a))))))))))))))))))))
            ( Cod
                ( PC
                    ( Cod
                        ( CC
                            ( Cod
                                ( MC (ValueL (ClosureL Id)) a
                                    ( Cod
                                        ( STC
                                            Rename
                                            RState
                                            ( Cod
                                                ( STC
                                                    CStore
                                                    Constraints
                                                    ( Cod
                                                        ( NDC
                                                            ( Cod
                                                                ( EC
                                                                    ( Cod
                                                                        ( STC
                                                                            Trace
                                                                            [TraceInfo]
                                                                            ( Cod
                                                                                ( IOC
                                                                                    ( L
                                                                                        a
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )

-- -- {-# SPECIALISE runCurryEffectsC :: [AEProg ((M ()) ())]
-- --                  -> (M ()) ()
-- --                  -> IO (Error [(Constraints, Value (Closure ()))]) #-}

runCurryEffectsC
    :: forall a
     . (Show a)
    => [AEProg ((M a) a)]
    -> (M a) a
    -> IO ([TraceInfo], Error [(Constraints, Value (Closure a))])
runCurryEffectsC ps e = do
    sup <- mkSplitUniqSupply 'a'
    let (sup1, sup2) = splitUniqSupply sup
        pipeline =
            finish
                . runStateC @Trace ([] :: [TraceInfo])
                . runErrorC
                . runNDC
                . runStateC @CStore Map.empty
                . runStateC' @Rename (initRenaming sup1)
                . runLazyC sup2
                . runConsC
                . runPartialC
                . runDeclC (Progs [])
    unIOC (pipeline (initDecls ps >> e))