{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Pipeline (
    runCurryEffects,
    runCurryEffectsC,
    runSmartCurryEffects,
    Result (..)
) where

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
import Transformation.AE2Result
import Type (Module, Ptr (..))
import Data.Char (chr)

runCurryEffects
    :: (Show a)
    => [Module (Prog (CurryEffects a) a)]
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
    :: [Module (SmartProg (CurryEffects ()) ())]
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
        ( DC (Progs Id a (Cod
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
    => [Module ((M a) a)]
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