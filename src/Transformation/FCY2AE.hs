{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# LANGUAGE TypeApplications #-}

module Transformation.FCY2AE (CurryEffects, fcyProg2ae, fcyRunner2ae) where

import Control.Monad (join, liftM2)
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
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Declarations (DeclF)
import Effect.FlatCurry.Function (
    Partial,
    apply,
    external,
    fun,
    lambda,
    partial, unlambda,
 )
import qualified Effect.FlatCurry.Function (CombType (..))
import Effect.FlatCurry.IO (IOAction)
import Effect.FlatCurry.Let
import Effect.General.Error (Err)
import Effect.General.Memoization
import Effect.General.ND (ND, failed, (?))
import Effect.General.State hiding (get, put)
import Free
import Signature
import Type (AEFuncDecl (..), AEPattern (..), Module (..), Args (..), single)

data VarKind
    = CombVar
    | LetVar
    | FreeVar
    | CaseVar
    deriving (Show)

type AEffects = '[Term, Renaming, ConstraintStore, ND, Err, StateF Trace [TraceInfo], IOAction]
type SEffects = '[Partial, Match]
type LEffects v = DeclF v :+++: (Thunking v :+++: LVoid)

type CurryEffects v = Sig AEffects SEffects (LEffects v) Id

-- normalform = id
fcyRunner2ae :: (TermMonad m (CurryEffects v)) => ARule TypeExpr -> m v
fcyRunner2ae (AExternal _ _) = undefined
fcyRunner2ae (ARule _ _ e) = unlambda $ normalform (join $ fcyExpr2ae [] e) -- normalform

fcyExpr2ae
    :: forall m v
     . (TermMonad m (CurryEffects v))
    => [VarIndex]
    -> AExpr TypeExpr
    -> m (m v)
fcyExpr2ae frees expr =
    let rec = fcyExpr2ae frees
     in case expr of
            AVar _ i -> do
              ptr <- lookupRenaming i
              if i `elem` frees then return $ fvar ptr 
                                else return $ lvar ptr
            ALit _ l -> return $ lit l
            AComb _ FuncCall (("Prelude", "?"), _) [e1, e2] ->
                liftM2 (?) (rec e1) (rec e2)
            AComb _ FuncCall (("Prelude", "failed"), _) [] -> return failed
            AComb _ FuncCall (("Prelude", "apply"), _) [fe, ee] ->
                liftM2 apply (rec fe) (fmap single (rec ee))
            AComb _ FuncCall (("Prelude", "dumpMemory"), _) [e] ->
                dumpMemory @v >> rec e
            AComb _ FuncCall (("Prelude", "$!"), _) [fe,ee] ->
              let pe = rec ee
              in liftM2 seq' pe (liftM2 apply (rec fe) (fmap single pe))
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
                fcyExpr2ae (vs ++ frees) e
            AOr _ e1 e2 -> do
                liftM2 (?) (rec e1) (rec e2)
            ACase _ _ e brs -> do
                let vs = map fst $ concatMap brVars brs
                vs' <- rename vs
                let r = zip vs vs'
                e' <- rec e
                brs' <-
                    mapM
                        (\(ABranch pat be) -> fmap (newPat r pat,) (rec be))
                        brs
                return $ case' e' brs'
              where
                newPat r (APattern _ (qn, _) vars) = AEPattern qn newVars
                  where
                    newVars = map (\(v, _) -> fromJust $ lookup v r) vars
                newPat _ (ALPattern _ l) = AELPattern l
            ATyped _ e _ -> rec e -- type annotations not required

brVars :: ABranchExpr a -> [(VarIndex, a)]
brVars (ABranch pat _) = case pat of
   ALPattern _ _  -> []
   APattern _ _ bs -> bs

fcyProg2ae :: (TermMonad m (CurryEffects v)) => AProg TypeExpr -> Module (m v)
fcyProg2ae (AProg name imports tdecls fdecls opdecls) =
    let fdecls' = map fcyFDecl2ae fdecls
        fdeclmap =
            Map.fromList
                (map (\fdecl@(AEFunc qn _ _ _ _) -> (qn, fdecl)) fdecls')
        tdeclmap = Map.fromList (map (\tdecl -> (typeName tdecl, tdecl)) tdecls)
     in Module name imports tdeclmap fdeclmap opdecls

fcyFDecl2ae
    :: (TermMonad m (CurryEffects v)) => AFuncDecl TypeExpr -> AEFuncDecl (m v)
fcyFDecl2ae (AFunc qn arity vis ty r) = AEFunc qn arity vis ty (fcyRule2ae r)

fcyRule2ae :: (TermMonad m (CurryEffects v)) => ARule TypeExpr -> m v
fcyRule2ae (ARule _ vars e) = do
    vs' <- rename (map fst vars)
    lambda vs' (join $ fcyExpr2ae [] e)
fcyRule2ae (AExternal _ s) = external s