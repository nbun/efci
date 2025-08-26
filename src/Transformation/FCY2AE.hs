{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Transformation.FCY2AE (CurryEffects, fcyProg2ae, fcyRunner2ae) where

import Control.Monad (join, liftM2, void)
import Curry.FlatCurry.Annotated.Goodies (typeName)
import Curry.FlatCurry.Annotated.Type (
    ABranchExpr (ABranch),
    AExpr (..),
    AFuncDecl (..),
    APattern (..),
    AProg (..),
    ARule (..),
    CombType (..),
    TypeExpr,
    VarIndex,
 )
import Data.Bifunctor (first)
import Data.IntMap (IntMap)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Debug.Trace (trace)
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Declarations (DeclF)
import Effect.FlatCurry.Function (
    Partial,
    apply,
    external,
    fun,
    lambda,
    partial, unReturn,
 )
import qualified Effect.FlatCurry.Function (CombType (..))
import Effect.FlatCurry.IO (IOAction)
import Effect.FlatCurry.Let
import Effect.General.Error (Err)
import Effect.General.Memoization
import Effect.General.ND (ND, failed, (?))
import Effect.General.Reader
import Effect.General.State (get, put)
import Effect.General.State hiding (get, put)
import Free
import Signature
import Type (AEFuncDecl (..), AEPattern (..), AEProg (..), Args (..), single)

data VarKind
    = CombVar
    | LetVar
    | FreeVar
    | CaseVar
    deriving (Show)

type VarKindMap = Map.Map VarIndex VarKind

type AEffects = '[ConsF, Renaming, ConstraintStore, ND, Err, StateF Trace [TraceInfo], IOAction]
type SEffects = '[Partial, CaseScope]
type LEffects v = DeclF v :+++: ((Thunking v :+++: LVoid))

type CurryEffects v = Sig AEffects SEffects (LEffects v) Id

-- normalform = id
fcyRunner2ae :: (TermMonad m (CurryEffects v)) => ARule TypeExpr -> m v
fcyRunner2ae (AExternal _ _) = undefined
fcyRunner2ae (ARule _ _ e) = unReturn $ normalform (join $ fcyExpr2ae [] e) -- normalform

fcyExpr2ae
    :: forall m v
     . (TermMonad m (CurryEffects v))
    => [VarIndex]
    -> AExpr TypeExpr
    -> m (m v)
fcyExpr2ae frees expr =
    let rec = fcyExpr2ae frees
     in case expr of
            AVar _ i
                | i `elem` frees -> do
                    j <- lookupRenaming i
                    return $ fvar j
                | otherwise -> do
                    j <- lookupRenaming i
                    return $ lvar j
            ALit _ l -> return $ lit l
            AComb _ FuncCall (("Prelude", "?"), _) [e1, e2] ->
                liftM2 (?) (rec e1) (rec e2)
            AComb _ FuncCall (("Prelude", "failed"), _) [] -> return failed
            AComb _ FuncCall (("Prelude", "apply"), _) [fe, ee] ->
                liftM2 apply (rec fe) (fmap single (rec ee))
            AComb _ callType (qn, _) args -> do
                args' <- mapM rec args
                case callType of
                    FuncCall -> return $ fun qn (Progs args')
                    FuncPartCall i ->
                        return $
                            partial qn (Effect.FlatCurry.Function.FuncPartCall i) args'
                    ConsCall -> return $ cons qn (Progs args')
                    ConsPartCall i ->
                        return $
                            partial qn (Effect.FlatCurry.Function.ConsPartCall i) args'
            -- _ -> error
            -- \$ "FCY2AE.fcyExpr2ae: comb type not supported for " ++ show qn
            ALet _ bs e -> do
                let ((vs, _), es) = first unzip (unzip bs)
                vs' <- rename vs
                es' <- mapM rec es
                e' <- rec e
                return $ let' vs' (Progs es') e'
            AFree _ bs e -> do
                let vs = map fst bs
                rename vs
                fcyExpr2ae (map fst bs ++ frees) e
            AOr _ e1 e2 -> do
                liftM2 (?) (rec e1) (rec e2)
            ACase _ ct e brs -> do
                let vs = map fst $ concatMap (patVars . (\(ABranch pat _) -> pat)) brs
                vs' <- rename vs
                let r = zip vs vs'
                e' <- rec e
                brs' <-
                    mapM
                        (\(ABranch pat e') -> fmap (newPat r pat,) (rec e'))
                        brs
                return $ case' e' brs'
              where
                newPat r (APattern _ (qn, _) vars) = AEPattern qn newVars
                  where
                    newVars = map (\(v, _) -> (fromJust $ lookup v r)) vars
                newPat _ (ALPattern _ l) = AELPattern l
            ATyped _ e t -> rec e -- type annotations not required

insertBinds :: VarKind -> VarKindMap -> [(VarIndex, ann)] -> VarKindMap
insertBinds k = foldl (\s' (v, _) -> Map.insert v k s')

patVars :: APattern ann -> [(VarIndex, ann)]
patVars (ALPattern _ _) = []
patVars (APattern _ _ bs) = bs

fcyProg2ae :: (TermMonad m (CurryEffects v)) => AProg TypeExpr -> AEProg (m v)
fcyProg2ae (AProg name imports tdecls fdecls opdecls) =
    let fdecls' = map fcyFDecl2ae fdecls
        fdeclmap =
            Map.fromList
                (map (\fdecl@(AEFunc qn _ _ _ _) -> (qn, fdecl)) fdecls')
        tdeclmap = Map.fromList (map (\tdecl -> (typeName tdecl, tdecl)) tdecls)
     in AEProg name imports tdeclmap fdeclmap opdecls

fcyFDecl2ae
    :: (TermMonad m (CurryEffects v)) => AFuncDecl TypeExpr -> AEFuncDecl (m v)
fcyFDecl2ae (AFunc qn arity vis ty r) = AEFunc qn arity vis ty (fcyRule2ae r)

fcyRule2ae :: (TermMonad m (CurryEffects v)) => ARule TypeExpr -> m v
fcyRule2ae (ARule _ vars e) = do
    vs' <- rename (fst $ unzip vars)
    lambda vs' (join $ (fcyExpr2ae [] e))
fcyRule2ae (AExternal _ s) = external s