{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Transformation.FCY2AE where

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
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Free (free)
import Effect.FlatCurry.Function (
  FunctionArgs,
  Partial,
  apply',
  fun,
  partial,
 )
import qualified Effect.FlatCurry.Function (CombType (..))
import Effect.FlatCurry.IO (IOAction)
import Effect.FlatCurry.Let
import Effect.General.Error (Err)
import Effect.General.Memoization
import Effect.General.ND (ND, failed, (?))
import Effect.General.Reader
import Effect.General.State hiding (get, put)
import Free
import Signature
import Type (AEFuncDecl (..), AEProg (..), AERule (..))

data VarKind
  = CombVar
  | LetVar
  | FreeVar
  | CaseVar
  deriving (Show)

type VarKindMap = Map.Map VarIndex VarKind

type AEF (f :: (* -> *) -> * -> *) v =
  ( ReaderF FunctionReader [AEProg (Prog f v)]
      :+: ConsF
      :+: StateF LocalBindings (IntMap Ptr)
      :+: Renaming
      :+: FunctionArgs
      :+: ND
      :+: Err
      :+: IOAction
  )

newtype AEffects v a = AEffects (AEF (CurryEffects v) v a)
  deriving (Functor)

instance
  (Functor sig, sig :<: AEF (CurryEffects v) v)
  => (:<:) sig (AEffects v)
  where
  inj = AEffects . inj

  prj (AEffects e) = prj e

type LEffects v = Thunking v :+++: LVoid

type SEffects = Partial :+: CaseScope :+: Void

type CurryEffects v = Sig (AEffects v) SEffects (LEffects v) Id

-- normalform = id
fcyRunner2ae :: (() :<<<: v) => ARule TypeExpr -> Prog (CurryEffects v) v
fcyRunner2ae (AExternal _ _) = undefined
fcyRunner2ae (ARule _ vars e) =
  let m = insertBinds CombVar Map.empty vars
   in normalform (join $ fcyExpr2ae m e) -- normalform

fcyExpr2ae
  :: forall v
   . (() :<<<: v)
  => VarKindMap
  -> AExpr TypeExpr
  -> Prog (CurryEffects v) (Prog (CurryEffects v) v)
fcyExpr2ae m expr = do
  case expr of
    AVar _ i -> case Map.lookup i m of
      Just k -> do
        scope <- currentScope
        case k of
          CombVar -> return $ lvar scope i
          LetVar -> return $ lvar scope i
          FreeVar -> return $ lvar scope i
          CaseVar -> return $ lvar scope i
      Nothing -> error $ "FCY2AE.fcyExpr2ae: Variable without kind: " ++ show i
    ALit _ l -> return $ lit l
    AComb _ FuncCall (("Prelude", "?"), _) [e1, e2] ->
      liftM2 (?) (fcyExpr2ae m e1) (fcyExpr2ae m e2)
    AComb _ FuncCall (("Prelude", "failed"), _) [] -> return failed
    AComb _ FuncCall (("Prelude", "apply"), _) [fe, ee] ->
      liftM2 apply' (fcyExpr2ae m fe) (fcyExpr2ae m ee)
    AComb _ callType (qn, _) args -> do
      args' <- mapM (fcyExpr2ae m) args
      case callType of
        FuncCall -> return $
          do
            scope <- newScope
            fun scope qn (Left args')
        FuncPartCall i ->
          return $
            partial qn (Effect.FlatCurry.Function.FuncPartCall i) args'
        ConsCall -> return $ cons qn args'
        ConsPartCall i ->
          return $
            partial qn (Effect.FlatCurry.Function.ConsPartCall i) args'
    -- _ -> error
    -- \$ "FCY2AE.fcyExpr2ae: comb type not supported for " ++ show qn
    ALet _ bs e -> do
      let ((vs, _), es) = first unzip (unzip bs)
          m' = insertBinds LetVar m (map fst bs)
      es' <- mapM (fcyExpr2ae m') es
      e' <- fcyExpr2ae m' e
      scope <- currentScope
      return $ let' scope (zip vs es') e'
    AFree _ bs e -> do
      let m' = insertBinds FreeVar m bs
      e' <- fcyExpr2ae m' e
      scope <- currentScope
      free scope bs e'
    AOr _ e1 e2 -> do
      liftM2 (?) (fcyExpr2ae m e1) (fcyExpr2ae m e2)
    ACase _ ct e brs -> do
      e' <- fcyExpr2ae m e
      brs' <-
        mapM
          ( \(ABranch pat e') ->
              fcyExpr2ae (insertBinds CaseVar m (patVars pat)) e'
                >>= \e'' -> return (patf pat, e'')
          )
          brs
      scope <- currentScope
      return $ case' scope e' brs'
     where
      patf (APattern _ (qn, _) vars) = APattern () (qn, ()) (map void vars)
      patf (ALPattern _ l) = ALPattern () l
    ATyped _ e t -> fcyExpr2ae m e -- type annotations not required

insertBinds :: VarKind -> VarKindMap -> [(VarIndex, ann)] -> VarKindMap
insertBinds k = foldl (\s' (v, _) -> Map.insert v k s')

patVars :: APattern ann -> [(VarIndex, ann)]
patVars (ALPattern _ _) = []
patVars (APattern _ _ bs) = bs

fcyProg2ae
  :: (() :<<<: v) => AProg TypeExpr -> AEProg (Prog (CurryEffects v) v)
fcyProg2ae (AProg name imports tdecls fdecls opdecls) =
  let fdecls' = map fcyFDecl2ae fdecls
      fdeclmap =
        Map.fromList
          (map (\fdecl@(AEFunc qn _ _ _ _) -> (qn, fdecl)) fdecls')
      tdeclmap = Map.fromList (map (\tdecl -> (typeName tdecl, tdecl)) tdecls)
   in AEProg name imports tdeclmap fdeclmap opdecls

fcyFDecl2ae
  :: (() :<<<: v) => AFuncDecl TypeExpr -> AEFuncDecl (Prog (CurryEffects v) v)
fcyFDecl2ae (AFunc qn arity vis ty r) = AEFunc qn arity vis ty (fcyRule2ae r)

fcyRule2ae
  :: (() :<<<: v) => ARule TypeExpr -> AERule (Prog (CurryEffects v) v)
fcyRule2ae (ARule _ vars e) =
  let (vs, _) = unzip vars
      m = insertBinds CombVar Map.empty vars
   in AERule vs (join $ fcyExpr2ae m e)
fcyRule2ae (AExternal _ s) = AEExternal s