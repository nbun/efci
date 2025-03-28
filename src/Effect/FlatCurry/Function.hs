{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}


module Effect.FlatCurry.Function where

import Curry.FlatCurry.Type (QName, VarIndex)

import Effect.FlatCurry.Constructor hiding (External)
import Effect.FlatCurry.Declarations (DeclF, getBody)
import Effect.FlatCurry.IO
import Effect.FlatCurry.Let
import Effect.General.Error
import Effect.General.Memoization
import Effect.General.ND
import Effect.General.State
import Free
import Signature
import Control.Monad (void)
import Type


type Functions sig sigs sigl a =
    ( '[ConsF, Err, IOAction, ConstraintStore, ND] :.: sig
    , '[Partial, CaseScope] :.: sigs
    , Thunking a :<<<<: sigl
    , Renaming :<: sig
    , DeclF a :<<<<: sigl
    , () :<<<: a
    , Let sig sigl a
    )

fun
    :: forall sig sigs sigl m a
     . (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => QName
    -> Args m a
    -> m a
fun qn args = logCallWith (show qn) >> do
  newRenamingScope
  apply (getBody qn) args

-- partial functions --

data CombType
    = FuncPartCall Int
    | ConsPartCall Int
    deriving (Show, Eq)

data Partial a
    = PartCall QName CombType [Ptr]
    | FApply a (Closure () -> a)
    | Abs [Ptr] Ptr
    | Ext String

instance Functor Partial where
    fmap _ (PartCall qn ct ptrs) = PartCall qn ct ptrs
    fmap f (FApply x k) = FApply (f x) (f . k)
    fmap f (Abs vs ptr) = Abs vs ptr
    fmap _ (Ext s) = Ext s
    {-# INLINE fmap #-}

data Closure a
    = Closure QName CombType [Ptr]
    | Lambda [Ptr] Ptr
    | External String
    | Other a
    deriving (Show)

instance Functor Closure where
    fmap _ (Closure qn ct ptrs) = Closure qn ct ptrs
    fmap f (Other x) = Other (f x)
    fmap _ (Lambda vs ptr) = Lambda vs ptr
    fmap _ (External s) = External s
    {-# INLINE fmap #-}

external :: (EffectCons m sig sigs sigl Id, Partial :<: sigs, Thunking a :<<<<: sigl) => String -> m a
external s = logCall >> injectS (Ext s)

lambda :: (EffectCons m sig sigs sigl Id, Partial :<: sigs, Thunking a :<<<<: sigl) => [Ptr] -> m a -> m a
lambda vs e = logCall >> do
    ptr <- store e
    injectS (Abs vs ptr)

partial
    :: (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, Partial :<: sigs)
    => QName
    -> CombType
    -> [m a]
    -> m a
partial qn combtype args =
    logCall >> do
        ptrs <- mapM store args
        injectS $ PartCall qn combtype ptrs

missingArgs :: CombType -> Int
missingArgs (FuncPartCall i) = i
missingArgs (ConsPartCall i) = i

decArgs :: CombType -> CombType
decArgs (FuncPartCall i) = FuncPartCall (i - 1)
decArgs (ConsPartCall i) = ConsPartCall (i - 1)

apply :: (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a) => m a -> Args m a -> m a
apply lam args = logCall >> do
    injectS $ FApply (fmap return lam) (return . k)
  where
    k (Lambda vs ptr) = let' vs args (force ptr)
    k (External s) = callExternal s args
    k (Closure qn combtype ptrs) = do
        new <- case args of
                 Progs ps -> mapM store ps
                 Thunks ptrs' -> return ptrs'
        let ptrs' = ptrs ++ new
         in case combtype of
                FuncPartCall 1 -> do
                    fun qn (Thunks ptrs')
                ConsPartCall 1 -> cons qn (Thunks ptrs')
                _ -> injectS $ PartCall qn (decArgs combtype) ptrs'
    k _ = undefined


callExternal
    :: (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => String
    -> Args m a
    -> m a
callExternal f args = logCall >> do
      let args' = case args of
                    Progs ps -> ps
                    Thunks ptrs -> map force ptrs
      case (f, args') of
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
            ) -> px >>= \x -> apply pf (single (return x))
        ("Prelude.getChar", []) -> getCharIO
        ("Prelude.prim_putChar", [pc]) -> putCharIO pc
        ("Prelude.prim_writeFile", [pfp, ps]) -> writeFileIO pfp (normalform ps)
        ("Prelude.prim_appendFile", [pfp, ps]) -> appendFileIO pfp (normalform ps)
        ("Prelude.prim_readFile", [pfp]) -> readFileIO pfp
        ("Prelude.ensureNotFree", [p]) -> p
        ("Prelude.$!", [pf, px]) -> apply pf (single px)
        ("Prelude.$##", [pf, px]) -> apply pf (single $ normalform px)
        ("Prelude.prim_error", [p]) -> err p
        ("Prelude.=:=", [px, py]) -> unify px py
        _ ->
            error $
                "Missing definition for "
                    ++ show f


runPartial
    :: forall sig sigs sigl l a
     . Prog (Sig sig (Partial :+: sigs) sigl l) a
    -> Prog (Sig sig sigs sigl (ClosureL l)) (Closure a)
runPartial = unPC . fold point con

runPartialSmart
    :: forall sig sigs sigl l a
     . SmartProg (Sig sig (Partial :+: sigs) sigl l) a
    -> SmartProg (Sig sig sigs sigl (ClosureL l)) (Closure a)
runPartialSmart = unPC . smartFold point con

instance
    (EffectMonad m sig sigs sigl (ClosureL l))
    => TermAlgebra (PC m) (Sig sig (Partial :+: sigs) sigl l)
    where
    con (A (Algebraic op)) = PC $ con (A (Algebraic (fmap unPC op)))
    con (S (Enter op)) = (algP # sfwd) op
      where
        algP (PartCall qn combtype args) = PC $ return $ Closure qn combtype args
        algP (FApply f k) = PC $
            do
                cl <- unPC f
                case cl of
                    Other x -> unPC x
                    _ -> do
                        t' <- unPC $ k (void cl)
                        (lift . fmap unPC) t'
        algP (Abs vs ptr) = PC $ return $ Lambda vs ptr
        algP (Ext s) = PC $ return $ External s
        sfwd op = PC $ con $ S $ Enter $ fmap (fmap lift . unPC . fmap unPC) op
    con (L (Node op l st k)) = PC $ con $ L $ Node op (ClosureL $ Other l) (st' st) k'
      where
        st' st2 c l' = lift2 (fmap (\x -> ClosureL <$> unPC (st2 c x)) (unClosureL l'))
        k' = lift . fmap (unPC . k) . unClosureL
    {-# INLINEABLE con #-}
    var = PC . gen'Reader
      where
        gen'Reader x = return (Other x)
    {-# INLINE var #-}

runPartialC
    :: (EffectMonad m sig sigs sigl (ClosureL l))
    => Cod (PC m) a
    -> m (Closure a)
runPartialC = unPC . runCod var
{-# INLINE runPartialC #-}

instance (Monad m) => Pointed (PC m) where
    point x = PC $ return (Other x)
    {-# INLINE point #-}

newtype PC m a = PC {unPC :: m (Closure a)}

instance (Functor m) => Functor (PC m) where
    fmap f (PC x) = PC (fmap (fmap f) x)
    {-# INLINE fmap #-}

instance Lift ClosureL Closure where
    lift (Closure qn ct ptrs) = return $ Closure qn ct ptrs
    lift (Lambda vs ptr) = return $ Lambda vs ptr
    lift (External s) = return $ External s
    lift (Other x) = x

    lift2 (Closure qn ct ptrs) = return $ ClosureL $ Closure qn ct ptrs
    lift2 (Lambda vs ptr) = return $ ClosureL $ Lambda vs ptr
    lift2 (External s) = return $ ClosureL $ External s
    lift2 (Other x) = x

newtype ClosureL l a = ClosureL {unClosureL :: Closure (l a)}
    deriving (Functor, Show)

-- unification --

unify
    :: forall sig sigs sigl m a
     . ( EffectCons m sig sigs sigl Id
       , ConsF :<: sig
       , Functions sig sigs sigl a
       , ND :<: sig
       , ConstraintStore :<: sig
       )
    => m a
    -> m a
    -> m a
unify e1 e2 =
    logCall
        >> injectS (Unify (fmap return e1) (fmap return e2) (return . cnt))
  where
    cnt :: (Value (), Value ()) -> m a
    cnt (HNF qn1 args1, HNF qn2 args2)
        | qn1 == qn2 = do
            let args1' = map force args1
            let args2' = map force args2
            ands $ zipWith unify args1' args2'
    cnt (Free i, Free j) = do
        modify @CStore (addC i (VarC j))
        cons ("Prelude", "True") (Progs [])
    cnt (Free i, HNF qn args) = do
        let args' = map force args
        vs <- freshNames (length args)
        let fvs = map fvar vs
        modify @CStore (addC i (ConsC qn vs))
        ands $ zipWith unify fvs args'
    cnt (HNF qn args, Free i) = cnt (Free i, HNF qn args)
    cnt (Lit l1, Lit l2)
        | l1 == l2 = cons ("Prelude", "True") (Progs [])
    cnt (Free i, Lit l) = do
        modify @CStore (addC i (LitC l))
        cons ("Prelude", "True") (Progs [])
    cnt (Lit l, Free i) = cnt (Free i, Lit l)
    cnt _ = failed

ands
    :: (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => [m a]
    -> m a
ands [] = cons ("Prelude", "True") (Progs [])
ands [x] = x
ands (x : xs) = do
    fun ("Prelude", "&&") (Progs [x, ands xs])