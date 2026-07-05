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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

{- | FlatCurry to effects transformation

This module transforms FlatCurry programs to an effect-based representation.
-}
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
    partial,
    unlambda,
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
import Type (AEFuncDecl (..), AEPattern (..), Args (..), Module (..), single)

{- | Algebraic effects for Curry interpretation

Includes core effects: Term, Renaming, ConstraintStore, ND, Err, Trace, IO.
-}
type AEffects = '[Term, Renaming, ConstraintStore, ND, Err, StateF Trace [TraceInfo], IOAction]

{- | Scoped effects for Curry interpretation

Includes Partial application and Match effects.
-}
type SEffects = '[Partial, Match]

{- | Latent effects for Curry interpretation

Includes Declarations and Memoization effects.
-}
type LEffects v = DeclF v :+++: (Thunking v :+++: LVoid)

{- | Complete Curry effects signature

Combines algebraic, scoped, and latent effects with the t'Id' latent carrier.
-}
type CurryEffects v = Sig AEffects SEffects (LEffects v) Id

{- | Transform a function rule to an effectful computation

Takes a FlatCurry @main@ function rule and converts it to an effectful computation.
External rules are not supported.
-}
fcyRunner2ae :: (TermMonad m (CurryEffects v)) => ARule TypeExpr -> m v
fcyRunner2ae (AExternal _ _) = undefined
fcyRunner2ae (ARule _ _ e) = unlambda $ normalform (join $ fcyExpr2ae [] e)

{- | Transform a FlatCurry expression to an effectful computation

Main expression transformation function that handles:
* Variables (with free variable detection)
* Literals
* Combinations (function calls, constructors, partial applications)
* Let expressions
* Free variables
* Non-deterministic branching
* Case expressions
* Type annotations (ignored)

Takes a list of free variable indices and transforms the expression to
an effectful computation with a two layers. The purpose of the layers
lies in providing the ability to rename variables independently of evaluating
the actual computation.
-}
fcyExpr2ae
    :: forall m v
     . (TermMonad m (CurryEffects v))
    => [VarIndex]
    -> AExpr TypeExpr
    -> m (m v)
fcyExpr2ae frees expr =
    let rec = fcyExpr2ae frees
    in  case expr of
            AVar _ i -> do
                ptr <- lookupRenaming i
                if i `elem` frees
                    then return $ fvar ptr
                    else return $ lvar ptr
            ALit _ l -> return $ lit l
            AComb _ FuncCall (("Prelude", "?"), _) [e1, e2] ->
                liftM2 (?) (rec e1) (rec e2)
            AComb _ FuncCall (("Prelude", "failed"), _) [] -> return failed
            AComb _ FuncCall (("Prelude", "apply"), _) [fe, ee] ->
                liftM2 apply (rec fe) (fmap single (rec ee))
            AComb _ FuncCall (("Prelude", "dumpMemory"), _) [e] ->
                dumpMemory @v >> rec e
            AComb _ FuncCall (("Prelude", "$!"), _) [fe, ee] ->
                let pe = rec ee
                in  liftM2 seq' pe (liftM2 apply (rec fe) (fmap single pe))
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

{- | Extract variable bindings from a branch expression

Used during case expression transformation to identify which variables
are bound by each pattern in the case alternatives.
-}
brVars :: ABranchExpr a -> [(VarIndex, a)]
brVars (ABranch pat _) = case pat of
    ALPattern _ _ -> []
    APattern _ _ bs -> bs

{- | Transform a complete FlatCurry program to a Module

Creates a Module containing the transformed function declarations,
type declarations, and operator declarations.

* Transforms all function declarations using 'fcyFDecl2ae'
* Creates maps for function and type declarations for efficient lookup
* Preserves the original program structure (name, imports, operator declarations)
-}
fcyProg2ae :: (TermMonad m (CurryEffects v)) => AProg TypeExpr -> Module (m v)
fcyProg2ae (AProg name imports tdecls fdecls opdecls) =
    let fdecls' = map fcyFDecl2ae fdecls
        fdeclmap =
            Map.fromList
                (map (\fdecl@(AEFunc qn _ _ _ _) -> (qn, fdecl)) fdecls')
        tdeclmap = Map.fromList (map (\tdecl -> (typeName tdecl, tdecl)) tdecls)
    in  Module name imports tdeclmap fdeclmap opdecls

{- | Transform a FlatCurry function declaration to an annotated effectful declaration

Preserves the function name, arity, visibility, and type information
while transforming the rule body using 'fcyRule2ae'.
-}
fcyFDecl2ae
    :: (TermMonad m (CurryEffects v)) => AFuncDecl TypeExpr -> AEFuncDecl (m v)
fcyFDecl2ae (AFunc qn arity vis ty r) = AEFunc qn arity vis ty (fcyRule2ae r)

{- | Transform a FlatCurry rule to an effectful computation

* For ARule: renames the variables and creates a lambda abstraction with the transformed body
* For AExternal: creates an external function reference
-}
fcyRule2ae :: (TermMonad m (CurryEffects v)) => ARule TypeExpr -> m v
fcyRule2ae (ARule _ vars e) = do
    vs' <- rename (map fst vars)
    lambda vs' (join $ fcyExpr2ae [] e)
fcyRule2ae (AExternal _ s) = external s