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

module Effect.FlatCurry.Function where

import Curry.FlatCurry.Type (QName, TypeExpr (..), VarIndex)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)

import Curry.FlatCurry.Annotated.Goodies (argTypes)
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Declarations (DeclF, getBody, getInfo)
import Effect.FlatCurry.IO
import Effect.FlatCurry.Let
import Effect.General.Error
import Effect.General.Memoization
import Effect.General.ND
import Effect.General.Reader
import Effect.General.State
import Free
import Signature
import Type (AEFuncDecl (..), AEProg (..), AERule (..))
import Effect.General.Delay


type Functions sig sigs sigl a =
    ( '[ConsF, Err, IOAction, ConstraintStore, ND] :.: sig
    , '[Partial, CaseScope] :.: sigs
    , Thunking a :<<<<: sigl
    , Delaying a :<<<<: sigl
    , Renaming :<: sig
    , DeclF a :<<<<: sigl
    , () :<<<: a
    , Let sig sigl a
    )

fun
    :: forall sig sigs sigl m a
     . (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => QName
    -> [m a]
    -> m a
fun qn ps = logCallWith (show qn) >> do
        modifyRenaming (const [])
        (ar, vis, ty, r) <- getInfo @a qn
        let fdecl = AEFunc qn ar vis ty r
        if isExternal fdecl
            then callExternal fdecl ps
            else do
                let (vs, _, _) = fdclRule fdecl
                let e = getBody qn
                let' (zip vs ps) e

callExternal
    :: (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => AEFuncDecl v
    -> [m a]
    -> m a
callExternal fdecl args = logCall >> case (externalName fdecl, args) of
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

instance Functor Partial where
    fmap _ (PartCall qn ct ptrs) = PartCall qn ct ptrs
    fmap f (FApply x k) = FApply (f x) (f . k)
    {-# INLINE fmap #-}

data Closure a
    = Closure QName CombType [Ptr]
    | Other a
    deriving (Show)

instance Vars a => Vars (Closure a) where
    vars (Closure _ _ ptrs) = ptrs
    vars (Other x) = vars x

instance Functor Closure where
    fmap _ (Closure qn ct ptrs) = Closure qn ct ptrs
    fmap f (Other x) = Other (f x)
    {-# INLINE fmap #-}

partial
    :: (EffectCons m sig sigs sigl Id, Delaying a :<<<<: sigl, Partial :<: sigs)
    => QName
    -> CombType
    -> [m a]
    -> m a
partial qn combtype args =
    logCall >> do
        ptrs <- mapM delay args
        injectS $ PartCall qn combtype ptrs

missingArgs :: CombType -> Int
missingArgs (FuncPartCall i) = i
missingArgs (ConsPartCall i) = i

decArgs :: CombType -> CombType
decArgs (FuncPartCall i) = FuncPartCall (i - 1)
decArgs (ConsPartCall i) = ConsPartCall (i - 1)

apply'
    :: (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => m a
    -> m a
    -> m a
apply' f x =
    logCall >> do
        ptr <- delay x
        injectS $ FApply (fmap return f) (return . k ptr)
  where
    k p (qn, combtype, ptrs) =
        let ptrs' = ptrs ++ [p]
         in case combtype of
                FuncPartCall 1 -> do
                    fun qn (map retrieve ptrs')
                ConsPartCall 1 -> thunkedCons qn ptrs'
                _ -> injectS $ PartCall qn (decArgs combtype) ptrs'

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
                t <- unPC f
                case t of
                    Other x -> unPC x
                    (Closure qn missing ptrs) -> do
                        t' <- unPC $ k (qn, missing, ptrs)
                        (lift . fmap unPC) t'

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
    lift (Other x) = x

    lift2 (Closure qn ct ptrs) = return $ ClosureL $ Closure qn ct ptrs
    lift2 (Other x) = x

newtype ClosureL l a = ClosureL {unClosureL :: Closure (l a)}
    deriving (Functor, Show)

instance Vars (Closure (l a)) => Vars (ClosureL l a) where
    vars (ClosureL c) = vars c

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
            let args1' = map (force) args1
            let args2' = map (force) args2
            ands $ zipWith unify args1' args2'
    cnt (Free i, Free j) = do
        modify @CStore (addC i (VarC j))
        cons ("Prelude", "True") []
    cnt (Free i, HNF qn args) = do
        let args' = map (force) args
        vs <- freshNames (length args)
        scope <- currentScope
        let fvs = map (fvar scope) vs
        modify @CStore (addC i (ConsC qn (map (scope,) vs)))
        ands $ zipWith unify fvs args'
    cnt (HNF qn args, Free i) = cnt (Free i, HNF qn args)
    cnt (Lit l1, Lit l2)
        | l1 == l2 = cons ("Prelude", "True") []
    cnt (Free i, Lit l) = do
        modify @CStore (addC i (LitC l))
        cons ("Prelude", "True") []
    cnt (Lit l, Free i) = cnt (Free i, Lit l)
    cnt _ = failed

ands
    :: (EffectCons m sig sigs sigl Id, Functions sig sigs sigl a)
    => [m a]
    -> m a
ands [] = cons ("Prelude", "True") []
ands [x] = x
ands (x : xs) = do
    fun ("Prelude", "&&") [x, ands xs]