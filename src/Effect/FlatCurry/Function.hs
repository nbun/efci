{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Effect.FlatCurry.Function where

import Curry.FlatCurry.Type (QName, TypeExpr (..), VarIndex)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Debug (ctrace)


import Curry.FlatCurry.Annotated.Goodies (argTypes)
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.IO
import Effect.FlatCurry.Let
import Effect.General.Error
import Effect.General.Memoization
import Effect.General.Reader
import Effect.General.State
import Free
import Signature
import Type (AEFuncDecl (..), AEProg (..), AERule (..))
import Effect.General.ND

data FunctionState

instance Identify FunctionState where
  identify = "FunctionState"

type FunctionArgs = StateF FunctionState [((Scope, TypeExpr), Ptr)]

type Functions sig sigs sigl a =
  ( '[Declarations sig sigs sigl a, FunctionArgs, ConsF, Err, IOAction, ConstraintStore, ND] :.: sig
  , '[Partial, CaseScope] :.: sigs
  , Let sig sigl a
  , () :<<<: a
  )

fun
  :: (Functions sig sigs sigl a)
  => Scope
  -> QName
  -> Either [Prog (Sig sig sigs sigl Id) a] [Ptr]
  -> Prog (Sig sig sigs sigl Id) a
fun scope qn ps = do
  ptrs <- case ps of
    Left exprs -> mapM thunk exprs
    Right ptrs -> return ptrs
  progs <- ask @FunctionReader
  let fdecl = findModule progs qn
  if isExternal fdecl
    then callExternal fdecl (map force ptrs)
    else do
      let (vs, ts, body) = fdclRule fdecl
          pds = findPolyDicts scope (zip ts ptrs)
      modify @FunctionState (pds ++)
      letThunked scope (zip vs ptrs) body

callExternal
  :: (Functions sig sigs sigl a)
  => AEFuncDecl v
  -> [Prog (Sig sig sigs sigl Id) a]
  -> Prog (Sig sig sigs sigl Id) a
callExternal fdecl args = case (externalName fdecl, args) of
  ("Prelude.plusInt", [px, py]) -> arithInt (+) px py
  ("Prelude.minusInt", [px, py]) -> arithInt (-) px py
  ("Prelude.timesInt", [px, py]) -> arithInt (*) px py
  ("Prelude.divInt", [px, py]) -> arithInt div px py
  ("Prelude.modInt", [px, py]) -> arithInt mod px py
  ("Prelude.eqInt", [px, py]) -> compInt (==) px py
  ("Prelude.ltEqInt", [px, py]) -> compInt (<=) px py
  ("Prelude.eqChar", [px, py]) -> compChar (==) px py
  ("Prelude.returnIO", [px]) -> px
  ( "Prelude.bindIO"
    , [px, pf]
    ) -> px >>= \x -> apply' pf (return x)
  ("Prelude.getChar", []) -> getCharIO
  ("Prelude.prim_putChar", [pc]) -> putCharIO pc
  ("Prelude.prim_writeFile", [pfp, ps]) -> writeFileIO pfp (normalform ps)
  ("Prelude.prim_appendFile", [pfp, ps]) -> appendFileIO pfp (normalform ps)
  ("Prelude.prim_readFile", [pfp]) -> readFileIO pfp
  ("Prelude.ensureNotFree", [p]) -> p
  ("Prelude.$!", [pf, px]) -> apply' pf px
  ("Prelude.$##", [pf, px]) -> apply' pf (normalform px)
  ("Prelude.prim_error", [p]) -> err p
  ("Prelude.=:=", [px, py]) -> unify px py
  _ ->
    error $
      "Missing definition for "
        ++ show (externalName fdecl)
        ++ " with "
        ++ show (length args)
        ++ " arguments"

findPolyDicts :: Scope -> [(TypeExpr, Ptr)] -> [((Scope, TypeExpr), Ptr)]
findPolyDicts s = mapMaybe isDict
 where
  isDict
    ( FuncType
        (TCons ("Prelude", "()") [])
        (TCons ("Prelude", "_Dict#Data") [TVar i])
      , ptr
      ) = Just ((s, TVar i), ptr)
  isDict _ = Nothing

fdclRule :: AEFuncDecl a -> ([VarIndex], [TypeExpr], a)
fdclRule (AEFunc qn _ _ t r) = case r of
  AERule vs e -> (vs, argTypes' t, e)
   where
    argTypes' (ForallType _ t) = argTypes t
    argTypes' t = argTypes t
  AEExternal s ->
    error $
      "Syntax.fdclExpr: external rule for " ++ show qn ++ " calling " ++ s

findModule :: [AEProg a] -> QName -> AEFuncDecl a
findModule ps qn@(mod, _) = case res of
  Just fdecl -> fdecl
  Nothing -> error $ "Function declaration " ++ show qn ++ " not found"
 where
  res =
    foldr
      ( \(AEProg name _ _ fdecls _) acc ->
          if name == mod
            then findFuncDecl fdecls qn
            else acc
      )
      Nothing
      ps

findFuncDecl :: Map.Map QName (AEFuncDecl a) -> QName -> Maybe (AEFuncDecl a)
findFuncDecl m qn = Map.lookup qn m

isExternal :: AEFuncDecl a -> Bool
isExternal (AEFunc _ _ _ _ r) = case r of
  AERule _ _ -> False
  AEExternal _ -> True

externalName :: AEFuncDecl a -> String
externalName (AEFunc _ _ _ _ r) = case r of
  AEExternal s -> s
  _ -> undefined

-- partial functions --

data CombType
  = FuncPartCall Int
  | ConsPartCall Int
  deriving (Show, Eq)

data Partial a
  = PartCall QName CombType [Ptr]
  | FApply a ((QName, CombType, [Ptr]) -> a)
  deriving (Functor)

data Closure a
  = Closure QName CombType [Ptr]
  | Other a
  deriving (Show, Functor)

partial
  :: (Functor sig, Functor sigs, Thunking a :<<<<: sigl, Partial :<: sigs)
  => QName
  -> CombType
  -> [Prog (Sig sig sigs sigl Id) a]
  -> Prog (Sig sig sigs sigl Id) a
partial qn combtype args = ctrace
  ("partial " ++ show qn ++ " " ++ show (missingArgs combtype))
  $ do
    ptrs <- mapM thunk args
    Call $ S $ Enter $ inj $ PartCall qn combtype ptrs

missingArgs :: CombType -> Int
missingArgs (FuncPartCall i) = i
missingArgs (ConsPartCall i) = i

decArgs :: CombType -> CombType
decArgs (FuncPartCall i) = FuncPartCall (i - 1)
decArgs (ConsPartCall i) = ConsPartCall (i - 1)

apply'
  :: (Functions sig sigs sigl a, Thunking a :<<<<: sigl)
  => Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
apply' f x = ctrace "apply" $
  do
    ptr <- thunk x
    injectS $ FApply (fmap return f) (return . k ptr)
 where
  k p (qn, combtype, ptrs) =
    let ptrs' = ptrs ++ [p]
     in case combtype of
          FuncPartCall 1 -> do
            scope <- newScope
            fun scope qn (Right ptrs')
          ConsPartCall 1 -> thunkedCons qn ptrs'
          _ -> injectS $ PartCall qn (decArgs combtype) ptrs'

runPartial
  :: forall sig sigs sigl l a
   . (Functor sig, Functor sigs)
  => Prog (Sig sig (Partial :+: sigs) sigl l) a
  -> Prog (Sig sig sigs sigl (ClosureL l)) (Closure a)
runPartial = unT . fold point (salg algP)
 where
  algP :: Partial (T sig sigs sigl l (T sig sigs sigl l x)) -> T sig sigs sigl l x
  algP (PartCall qn combtype args) = T $ return $ Closure qn combtype args
  algP (FApply f k) = T $
    do
      t <- unT f
      case t of
        Other x -> unT x
        (Closure qn missing ptrs) -> do
          t' <- unT $ k (qn, missing, ptrs)
          (lift . fmap unT) t'

newtype T sig sigs sigl l a = T {unT :: Prog (Sig sig sigs sigl (ClosureL l)) (Closure a)}
  deriving (Functor)

instance Forward T where
  afwd op = T $ Call $ A $ Algebraic $ fmap unT op
  sfwd op = T $ Call $ S $ Enter $ fmap (fmap lift . unT . fmap unT) op
  lfwd op l st k = T $ Call $ L $ Node op (ClosureL $ Other l) (st' st) k'
   where
    st' st2 c l' = lift2 (fmap (\x -> ClosureL <$> unT (st2 c x)) (unClosureL l'))
    k' = lift . fmap (unT . k) . unClosureL

instance Lift ClosureL Closure where
  lift (Closure qn ct ptrs) = return $ Closure qn ct ptrs
  lift (Other x) = x

  lift2 (Closure qn ct ptrs) = return $ ClosureL $ Closure qn ct ptrs
  lift2 (Other x) = x

newtype ClosureL l a = ClosureL {unClosureL :: Closure (l a)}
  deriving (Functor, Show)

instance (Functor sig, Functor sigs) => Pointed (T sig sigs sigl l) where
  point x = T $ return $ Other x

-- unification --

unify :: forall sig sigs sigl m a. ( ConsF :<: sig
         , Functions sig sigs sigl a
         , ND :<: sig
         , ConstraintStore :<: sig)
      => Prog (Sig sig sigs sigl Id) a
      -> Prog (Sig sig sigs sigl Id) a
      -> Prog (Sig sig sigs sigl Id) a
unify e1 e2 = ctrace "unify"
  $ injectS (Unify (fmap return e1) (fmap return e2) (return . cnt))
  where
    cnt :: (Value (), Value ()) -> Prog (Sig sig sigs sigl Id) a
    cnt (HNF qn1 args1, HNF qn2 args2)
      | qn1 == qn2 = ctrace ("unify: " ++ show qn1 ++ " " ++ show qn2)
        $ do
          let args1' = map force args1
          let args2' = map force args2
          ands $ zipWith unify args1' args2'
    cnt (Free i, Free j) = do
      modify @CStore (addC i (VarC j))
      cons ("Prelude", "True") []
    cnt (Free i, HNF qn args) = ctrace ("unify: " ++ show i ++ " " ++ show qn)
      $ do
        let args' = map force args
        cs <- get @CStore
        scope <- currentScope
        vs <- freshNames scope (length args)
        let fvs = map (fvar scope) vs
        put @CStore (addC i (ConsC qn vs) cs)
        ands $ zipWith unify fvs args'
    cnt (HNF qn args, Free i) = cnt (Free i, HNF qn args)
    cnt (Lit l1, Lit l2)
      | l1 == l2 = cons ("Prelude", "True") []
    cnt (Free i, Lit l) = ctrace ("unify: " ++ show i ++ " " ++ show l)
      $ do
        modify @CStore (addC i (LitC l))
        cons ("Prelude", "True") []
    cnt (Lit l, Free i) = cnt (Free i, Lit l)
    cnt args = ctrace ("unify: fail: " ++ show args) failed

ands :: (Functions sig sigs sigl a)
     => [Prog (Sig sig sigs sigl Id) a]
     -> Prog (Sig sig sigs sigl Id) a
ands [] = cons ("Prelude", "True") []
ands [x] = x
ands (x:xs) = do
  scope <- newScope
  fun scope ("Prelude", "&&") (Left [x, ands xs])