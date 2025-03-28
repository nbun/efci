{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}

module Effect.FlatCurry.Constructor where

import Control.Monad (void)
import Curry.FlatCurry.Annotated.Type (APattern (..), Literal (..), VarIndex)
import Curry.FlatCurry.Type (CaseType (..), QName)
import Data.Functor ((<&>))
import Data.Maybe (mapMaybe)
import Effect.FlatCurry.Let
import Effect.General.Error (Err (..))
import Effect.General.Memoization
import Effect.General.ND (ND, choose, failed)
import Effect.General.State
import Free
import Signature
import Type

data ConsF a
    = FCons QName [Ptr]
    | FStrictCons QName [a]
    | FLit Literal
    | FFree Ptr

instance Functor ConsF where
    fmap _ (FCons qn args) = FCons qn args
    fmap f (FStrictCons qn args) = FStrictCons qn (map f args)
    fmap _ (FLit l) = FLit l
    fmap _ (FFree i) = FFree i
    {-# INLINE fmap #-}

data CaseScope a
    = Case a (Value () -> a)
    | Normalize a ((QName, [Ptr]) -> a)
    | External [a] ([Value ()] -> a)
    | Unify a a ((Value (), Value ()) -> a)

instance Functor CaseScope where
    fmap f (Case a k) = Case (f a) (f . k)
    fmap f (Normalize a k) = Normalize (f a) (f . k)
    fmap f (External as k) = External (map f as) (f . k)
    fmap f (Unify a1 a2 k) = Unify (f a1) (f a2) (f . k)
    {-# INLINE fmap #-}

data Mode
    = Strict
    | Lazy CaseType
    deriving (Eq, Show)

normalform
    :: ( ConsF :<: sig
       , Thunking a :<<<<: sigl
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => m a
    -> m a
normalform p = logCall >> injectS (Normalize (fmap return p) (fmap return . f))
  where
    f (qn, ptrs) = do
        let args = map ((normalform . force)) ptrs
        injectA (FStrictCons qn args)
{-# INLINE normalform #-}

cons
    :: (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, ConsF :<: sig)
    => QName
    -> Args m a
    -> m a
cons qn args =
    logCall >> do
        ptrs <- foldArgs (mapM store) return args
        injectA (FCons qn ptrs)
{-# INLINE cons #-}

lit :: (EffectCons m sig sigs sigl l, ConsF :<: sig) => Literal -> m a
lit l = logCall >> injectA (FLit l)
{-# INLINE lit #-}

data CaseState

instance Identify CaseState where
    identify = "CaseState"

case'
    :: forall m sig sigs sigl a
     . (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, Renaming :<: sig, CaseScope :<: sigs, ND :<: sig, ConstraintStore :<: sig, ConsF :<: sig)
    => m a
    -> [(AEPattern, m a)]
    -> m a
case' cp brs =
    logCall
        >> injectS (Case (fmap return cp) (return . cnt))
  where
    cnt :: Value () -> m a
    cnt hnf = case mapMaybe (match hnf) brs of
        [] -> failed
        [x] -> x
        xs -> choose xs
      where
        match (HNF qn args) (AEPattern pqn argPtrs, e)
            | pqn == qn =
                Just $ let' argPtrs (Thunks args) e
            | otherwise = Nothing
        match (Lit l) (AELPattern lp, e)
            | l == lp = Just e
            | otherwise = Nothing
        match (Free i) pat = Just $ do
            case pat of
                (AEPattern pqn argPtrs, e) -> do
                    vs <- freshNames (length argPtrs)
                    let fvs = Progs $ map fvar vs
                    modify @CStore (addC i (ConsC pqn vs))
                    let' argPtrs fvs e
                (AELPattern lp, e) -> do
                    modify @CStore (addC i (LitC lp))
                    e
        match v ps =
            error $
                "Pattern match not implemented for " ++ show v ++ show (fst ps)

data Value a
    = Cons QName [Value a]
    | HNF QName [Ptr]
    | Lit Literal
    | Free Ptr
    | ValOther a
    deriving Show

instance Functor Value where
    fmap f (Cons qn args) = Cons qn (map (fmap f) args)
    fmap _ (HNF qn ptrs) = HNF qn ptrs
    fmap _ (Lit l) = Lit l
    fmap _ (Free i) = Free i
    fmap f (ValOther x) = ValOther (f x)
    {-# INLINE fmap #-}

newtype ValueL l a = ValueL {unValueL :: Value (l a)}
    deriving (Show)

instance (Functor l) => Functor (ValueL l) where
    fmap f (ValueL x) = ValueL (fmap (fmap f) x)
    {-# INLINE fmap #-}

runCons
    :: forall sig sigs sigl l a
     . Prog (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l) a
    -> Prog (Sig sig sigs sigl (ValueL l)) (Value a)
runCons = unCC . fold point con
{-# INLINE runCons #-}

runConsSmart
    :: forall sig sigs sigl l a
     . SmartProg (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l) a
    -> SmartProg (Sig sig sigs sigl (ValueL l)) (Value a)
runConsSmart = unCC . smartFold point con
{-# INLINE runConsSmart #-}

instance
    (EffectMonad m sig sigs sigl (ValueL l))
    => TermAlgebra (CC m) (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l)
    where
    con (A (Algebraic op)) = CC . (algCa # afwd) . fmap unCC $ op
      where
        algCa (FCons qn args) = return (HNF qn args)
        algCa (FStrictCons qn args) = sequence args <&> Cons qn
        algCa (FLit l) = return (Lit l)
        algCa (FFree i) = return (Free i)

        afwd = con . A . Algebraic
    con (S (Enter op)) = (algCs # sfwd) op
      where
        algCs (Case ce k) = CC $ do
            hnf <- unCC ce
            unCC (k (void hnf)) >>= lift'
        algCs (Normalize ce k) = CC $
            do
                hnf <- unCC ce
                case hnf of
                    HNF qn args -> do
                        hnf <- unCC (k (qn, args))
                        case hnf of
                            Cons qn args -> mapM lift' args <&> Cons qn
                            Lit l -> return $ Lit l
                            _ -> undefined
                    Lit l -> return $ Lit l
                    Free i -> return $ Free i
                    Cons qn args -> mapM lift' args <&> Cons qn
                    ValOther x -> unCC x
        algCs (External ps k) = CC $
            do
                hnfs <- mapM unCC ps
                hnf <- unCC $ k (map void hnfs)
                lift' hnf
        algCs (Unify e1 e2 k) = CC $
            do
                hnf1 <- unCC e1
                hnf2 <- unCC e2
                hnf <- unCC (k (void hnf1, void hnf2))
                lift' hnf

        lift' = lift . fmap unCC
        sfwd op = CC $ con $ S $ Enter $ fmap (fmap lift . unCC . fmap unCC) op
    con (L (Node op l st k)) = CC $ con $ L $ Node op (ValueL $ ValOther l) (st' st) k'
      where
        st' st2 c l' = lift2 (fmap (\x -> ValueL <$> unCC (st2 c x)) (unValueL l'))
        k' = lift . fmap (unCC . k) . unValueL
    {-# INLINE con #-}
    var = CC . gen'Error
      where
        gen'Error x = return (ValOther x)
    {-# INLINE var #-}

runConsC :: (EffectMonad m sig sigs sigl (ValueL l)) => Cod (CC m) a -> m (Value a)
runConsC = unCC . runCod var
{-# INLINE runConsC #-}

newtype CC m a = CC {unCC :: m (Value a)}
    deriving (Functor)

instance (Monad m) => Pointed (CC m) where
    point x = CC $ return (ValOther x)
    {-# INLINE point #-}

instance Lift ValueL Value where
    lift (Cons qn args) = mapM lift args <&> Cons qn
    lift (HNF qn ptrs) = return $ HNF qn ptrs
    lift (Lit l) = return $ Lit l
    lift (Free i) = return $ Free i
    lift (ValOther x) = x

    lift2 (Cons qn args) = mapM lift2 args <&> ValueL . Cons qn . map unValueL
    lift2 (HNF qn ptrs) = return $ ValueL $ HNF qn ptrs
    lift2 (Lit l) = return $ ValueL $ Lit l
    lift2 (Free i) = return $ ValueL $ Free i
    lift2 (ValOther x) = x

arithInt
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl l)
    => (Integer -> Integer -> Integer)
    -> m a
    -> m a
    -> m a
arithInt op x y = logCall >> injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Intc x), Lit (Intc y)] = lit (Intc (x `op` y))
{-# INLINE arithInt #-}

compInt
    :: ( ConsF :<: sig
       , Thunking v :<<<<: sigl
       , ConsF :<: sig
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Integer -> Integer -> Bool)
    -> m v
    -> m v
    -> m v
compInt op x y = logCall >> injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Intc x), Lit (Intc y)]
        | x `op` y = cons ("Prelude", "True") (Progs [])
        | otherwise = cons ("Prelude", "False") (Progs [])
{-# INLINE compInt #-}

compChar
    :: ( ConsF :<: sig
       , Thunking v :<<<<: sigl
       , ConsF :<: sig
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Char -> Char -> Bool)
    -> m v
    -> m v
    -> m v
compChar op x y =
    logCall >> injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Charc x), Lit (Charc y)]
        | x `op` y = cons ("Prelude", "True") (Progs [])
        | otherwise = cons ("Prelude", "False") (Progs [])
{-# INLINE compChar #-}

err
    :: forall sig sigs sigl m v
     . ( CaseScope :<: sigs
       , Err :<: sig
       , Thunking v :<<<<: sigl
       , EffectCons m sig sigs sigl Id
       )
    => m v
    -> m v
err p =
    logCall >> injectS (External [fmap return p] (return . f))
  where
    f :: [Value ()] -> m v
    f [hnf] = injectA (Err (val2str hnf))
{-# INLINE err #-}

val2str :: (Show a) => Value a -> [Char]
val2str (Cons ("Prelude", "[]") []) = ""
val2str (Cons ("Prelude", ":") [Lit (Charc c), xs]) = c : val2str xs
val2str hnf = error $ "hnf2str: " ++ show hnf

str2prog
    :: (Thunking a :<<<<: sigl, ConsF :<: sig, EffectCons m sig sigs sigl Id)
    => String
    -> m a
str2prog [] = cons ("Prelude", "[]") (Progs [])
str2prog (c : cs) = cons ("Prelude", ":") (Progs [lit (Charc c), str2prog cs])

-- free variables --

fvar
    :: ( ConsF :<: sig
       , Thunking a :<<<<: sigl
       , ConstraintStore :<: sig
       , Renaming :<: sig
       , EffectCons m sig sigs sigl Id
       )
    => Ptr
    -> m a
fvar i =
    logCall >> do
        cs <- get @CStore
        applyC cs i
  where
    applyC store n = case lookupC n store of
        Just (ConsC qn vs) -> do
            cons qn (Progs $ map (applyC store) vs)
        Just (VarC j) -> applyC store j
        Just (LitC l) -> lit l
        _ -> injectA $ FFree n