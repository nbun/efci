{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveTraversable #-}

module Effect.FlatCurry.Function (
    apply,
    fun,
    partial,
    lambda,
    external,
    Partial,
    CombType (..),
    Closure (..),
    ClosureL (..),
    PC,
    runPartial,
    runPartialSmart,
    missingArgs,
    runPartialC,
    unlambda,
) where

import Curry.FlatCurry.Type (QName)

import Control.Monad (void)
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Declarations (DeclF, getBody)
import Effect.FlatCurry.IO
import Effect.FlatCurry.Let
import Effect.General.Error
import Effect.General.Memoization
import Effect.General.ND
import Effect.General.State
import Free
import Signature
import Type

type Functions sig sigs sigl a =
    ( '[Term, Err, IOAction, ConstraintStore, Renaming, ND] :.: sig
    , '[Partial, Match] :.: sigs
    , Thunking a :<<<<: sigl
    , DeclF a :<<<<: sigl
    )

fun
    :: forall sig sigs sigl m a
     . (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => QName
    -> Args m a
    -> m a
fun qn args = 
    logCallWith (fst qn ++ "." ++ snd qn) False >> do
        newRenamingScope qn
        apply (getBody qn) args
{-# INLINE fun #-}

-- partial functions --

data CombType
    = FuncPartCall Int
    | ConsPartCall Int
    deriving (Show, Eq)

data Partial a
    = PartCall QName CombType [Ptr]
    | Apply a (Closure () -> a)
    | Abs [Ptr] Ptr
    | Ext String
    deriving (Functor)

data Closure a
    = Closure QName CombType [Ptr]
    | Lambda [Ptr] Ptr
    | External String
    | Other a
    deriving (Functor, Show, Foldable, Traversable)

instance Applicative Closure where
    pure = Other
    {-# INLINE pure #-}
    Other f <*> x = fmap f x
    Closure qn ct ptrs <*> _ = Closure qn ct ptrs
    Lambda vs ptr <*> _ = Lambda vs ptr
    External s <*> _ = External s

instance Monad Closure where
    Other x >>= f = f x
    Closure qn ct ptrs >>= _ = Closure qn ct ptrs
    Lambda vs ptr >>= _ = Lambda vs ptr
    External s >>= _ = External s

instance Pointed Closure where
    point = Other
    {-# INLINE point #-}

external :: (EffectCons m sig sigs sigl Id, Partial :<: sigs) => String -> m a
external s = logPrimCall >> injectS (Ext s)

lambda :: (EffectCons m sig sigs sigl Id, Partial :<: sigs, Thunking a :<<<<: sigl) => [Ptr] -> m a -> m a
lambda vs e =
    logPrimCall >> do
        ptr <- store "lambda" e
        injectS (Abs vs ptr)

partial
    :: (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, Partial :<: sigs)
    => QName
    -> CombType
    -> [m a]
    -> m a
partial qn combtype args =
    logPrimCall >> do
        ptrs <- mapM (store (fst qn ++ "." ++ snd qn ++ ".partial")) args
        injectS $ PartCall qn combtype ptrs

missingArgs :: CombType -> Int
missingArgs (FuncPartCall i) = i
missingArgs (ConsPartCall i) = i

decArgs :: CombType -> Int -> CombType
decArgs (FuncPartCall i) n = FuncPartCall (i - n)
decArgs (ConsPartCall i) n = ConsPartCall (i - n)

unlambda :: forall m sig sigs sigl a. (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a) => m a -> m a
unlambda lam = apply lam (Progs [])
{-# INLINE unlambda #-}

apply :: forall m sig sigs sigl a. (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a) => m a -> Args m a -> m a
apply lam args =
    logPrimCall >> do
        injectS $ Apply (fmap return lam) (return . k)
  where
    k :: Closure () -> m a
    k (Lambda vs ptr) = let' vs args (retrieve ptr)
    k (External s) = callExternal s args
    k (Closure qn combtype ptrs) = do
        new <- case args of
            Progs ps -> mapM (store (fst qn ++ "." ++ snd qn ++ ".closure")) ps
            Thunks ptrs' -> return ptrs'
        let ptrs' = ptrs ++ new
            n = length new
         in case combtype of
                FuncPartCall missing | missing == n -> do
                    fun qn (Thunks ptrs')
                ConsPartCall missing | missing == n -> cons qn (Thunks ptrs')
                _ -> injectS $ PartCall qn (decArgs combtype n) ptrs'
    k (Other _) = error "apply: Other encountered"

callExternal
    :: forall m sig sigs sigl a
     . (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => String
    -> Args m a
    -> m a
callExternal f args =
    logCall >> do
        let args' = case args of
                Progs ps -> ps
                Thunks ptrs -> map force ptrs
        case (drop 8 f, args') of -- drop 'Prelude.' prefix
            ("plusInt", [px, py]) -> arithInt (+) px py
            ("minusInt", [px, py]) -> arithInt (-) px py
            ("timesInt", [px, py]) -> arithInt (*) px py
            ("divInt", [px, py]) -> arithInt div px py
            ("modInt", [px, py]) -> arithInt mod px py
            ("remInt", [px, py]) -> arithInt rem px py

            ("eqInt", [px, py]) -> compInt (==) px py
            ("ltEqInt", [px, py]) -> compInt (<=) px py
            ("eqFloat", [px, py]) -> compFloat (==) px py
            ("ltEqFloat", [px, py]) -> compFloat (<=) px py

            ("plusFloat", [px, py]) -> arithFloat (+) px py
            ("minusFloat", [px, py]) -> arithFloat (-) px py
            ("timesFloat", [px, py]) -> arithFloat (*) px py
            ("divFloat", [px, py]) -> arithFloat (/) px py

            ("negateFloat", [px]) -> arithFloat2Float negate px
            ("logFloat", [px]) -> arithFloat2Float log px
            ("expFloat", [px]) -> arithFloat2Float exp px
            ("sqrtFloat", [px]) -> arithFloat2Float sqrt px
            ("sinFloat", [px]) -> arithFloat2Float sin px
            ("cosFloat", [px]) -> arithFloat2Float cos px
            ("tanFloat", [px]) -> arithFloat2Float tan px
            ("asinFloat", [px]) -> arithFloat2Float asin px
            ("acosFloat", [px]) -> arithFloat2Float acos px
            ("atanFloat", [px]) -> arithFloat2Float atan px
            ("sinhFloat", [px]) -> arithFloat2Float sinh px
            ("coshFloat", [px]) -> arithFloat2Float cosh px
            ("tanhFloat", [px]) -> arithFloat2Float tanh px
            ("asinhFloat", [px]) -> arithFloat2Float asinh px
            ("acoshFloat", [px]) -> arithFloat2Float acosh px
            ("atanhFloat", [px]) -> arithFloat2Float atanh px
            ("truncateFloat", [px]) -> arithFloat2Int truncate px
            ("roundFloat", [px]) -> arithFloat2Int round px

            ("intToFloat", [px]) -> arithInt2Float fromInteger px

            ("eqChar", [px, py]) -> compChar (==) px py
            ("ltEqChar", [px, py]) -> compChar (<=) px py
            ("ord", [px]) -> ordChar px
            ("chr", [px]) -> chrChar px

            
            ("returnIO", [px]) -> returnIO px
            ("bindIO"
                , [px, pf]
                ) -> bindIO px pf
            ("getChar", []) -> getCharIO
            ("prim_putChar", [pc]) -> putCharIO pc
            ("prim_writeFile", [pfp, ps]) -> writeFileIO pfp (normalform ps)
            ("prim_appendFile", [pfp, ps]) -> appendFileIO pfp (normalform ps)
            ("prim_readFile", [pfp]) -> readFileIO pfp
            
            ("ensureNotFree", [p]) -> eval2HNF p >> p
            ("$!", [pf, px]) -> eval2HNF px >> apply pf (single px)
            ("$##", [pf, px]) -> apply pf (single $ normalform px)
            ("prim_error", [p]) -> err p
            ("=:=", [_, px, py]) -> unify px py

            ("prim_showStringLiteral", [ps]) -> ps
            ("prim_showCharLiteral", [pc]) -> showCharLiteral pc
            ("prim_showIntLiteral", [p]) -> showIntLiteral p
            ("prim_showFloatLiteral", [pf]) -> showFloatLiteral pf

            ("prim_readCharLiteral", [ps]) -> readCharLiteral ps
            ("prim_readIntLiteral", [ps]) -> readIntLiteral ps
            ("prim_readFloatLiteral", [ps]) -> readFloatLiteral ps
            ("prim_readStringLiteral", [ps]) -> readStringLiteral ps

            ("dumpMemory", [p]) -> dumpMemory @a >> p
            _ ->
                error $
                    "Missing definition for "
                        ++ show f
                        ++ " with arity "
                        ++ show (length args')

returnIO :: (EffectCons m sig sigs sigl Id, Partial :<: sigs, Thunking a :<<<<: sigl, Renaming :<: sig) 
          => m a -> m a
returnIO = lambda []
{-# INLINE returnIO #-}

bindIO :: (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, Functions sig sigs sigl a) 
          => m a -> m a -> m a
bindIO px pf = eval2HNF px >> apply pf (single (unlambda px))
{-# INLINE bindIO #-}

runPartial
    :: (EffectMonad m sig sigs sigl (ClosureL l))
    => Prog (Sig sig (Partial :+: sigs) sigl l) a
    -> m (Closure a)
runPartial = unPC . fold point con
{-# INLINE runPartial #-}

runPartialSmart
    :: (EffectMonad m sig sigs sigl (ClosureL l))
    => SmartProg (Sig sig (Partial :+: sigs) sigl l) a
    -> m (Closure a)
runPartialSmart = unPC . smartFold point con
{-# INLINE runPartialSmart #-}

instance LCarrier ClosureL Closure where
    lift (Closure qn ct ptrs) = pure $ Closure qn ct ptrs
    lift (Lambda vs ptr) = pure $ Lambda vs ptr
    lift (External s) = pure $ External s
    lift (Other x) = x

    lift2 (Closure qn ct ptrs) = pure $ ClosureL $ Closure qn ct ptrs
    lift2 (Lambda vs ptr) = pure $ ClosureL $ Lambda vs ptr
    lift2 (External s) = pure $ ClosureL $ External s
    lift2 (Other x) = x

instance OuterCarrier PC Closure
instance DeriveForward 'Outer PC ClosureL

algP :: (Monad m, LCarrier cL Closure, TermAlgebra m (Sig sig sigs sigl (cL l)), Pointed m  ) => Partial (m (Closure (m (Closure a)))) -> m (Closure a)
algP (PartCall qn combtype args) = return $ Closure qn combtype args
algP (Apply p k) = do
    clsr <- p
    case clsr of
        Other x -> x
        _ -> k (void clsr) >>= lift
algP (Abs vs ptr) = return $ Lambda vs ptr
algP (Ext s) = return $ External s

instance
    (EffectMonad m sig sigs sigl (ClosureL l))
    => TermAlgebra (PC m) (Sig sig (Partial :+: sigs) sigl l)
    where
    con (A op) = afwd op
    con (S (Enter op)) = ((PC . algP . fmap (unPC . fmap unPC)) # (sfwd . Enter)) op
    con (L op) = lfwd op
    {-# INLINE con #-}
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

instance (Pointed m) => Pointed (PC m) where
    point x = PC $ point (Other x)
    {-# INLINE point #-}

newtype PC m a = PC {unPC :: m (Closure a)}

instance (Functor m) => Functor (PC m) where
    fmap f (PC x) = PC (fmap (fmap f) x)
    {-# INLINE fmap #-}

newtype ClosureL l a = ClosureL {unClosureL :: Closure (l a)}
    deriving (Functor, Show)

-- unification --

unify
    :: forall sig sigs sigl m a
     . ( EffectCons m sig sigs sigl Id
       , Term :<: sig
       , Functions sig sigs sigl a
       , ND :<: sig
       , ConstraintStore :<: sig
       )
    => m a
    -> m a
    -> m a
unify e1 e2 =
    logPrimCall
        >> injectS (Match (map (fmap return) [e1,e2]) (return . cnt))
  where
    cnt :: [Value ()] -> m a
    cnt [HNF qn1 args1, HNF qn2 args2]
        | qn1 == qn2 = do
            let args1' = map force args1
            let args2' = map force args2
            ands $ zipWith unify args1' args2'
    cnt [Free i, Free j] = do
        modify @CStore (addC i (VarC j))
        true
    cnt [Free i, HNF qn args] = do
        let args' = map force args
        vs <- freshNames (length args)
        let fvs = map fvar vs
        modify @CStore (addC i (ConsC qn vs))
        ands $ zipWith unify fvs args'
    cnt [HNF qn args, Free i] = cnt [Free i, HNF qn args]
    cnt [Lit l1, Lit l2]
        | l1 == l2 = true
    cnt [Free i, Lit l] = do
        modify @CStore (addC i (LitC l))
        true
    cnt [Lit l, Free i] = cnt [Free i, Lit l]
    cnt _ = failed

ands
    :: (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => [m a]
    -> m a
ands [] = true
ands [x] = x
ands (x : xs) = do
    fun ("Prelude", "&&") (Progs [x, ands xs])