{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

module Effect.General.ND (
    choose,
    failed,
    ND,
    (?),
    runND,
    runNDC,
    runNDSmart,
    ListL,
    NDC,
) where

import Control.Monad (liftM2)
import Effect.General.State (EffectCons, logCall)
import Free
import GHC.Conc
import Signature

data ND a = Fail | Or a a

instance Functor ND where
    fmap _ Fail = Fail
    fmap f (Or l r) =
        let l' = f l
            r' = f r
         in pseq (par l' r') (Or l' r')
    {-# INLINE fmap #-}

(?)
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => m a
    -> m a
    -> m a
(?) p1 p2 = logCall >> injectA (Or p1 p2)
{-# INLINE (?) #-}

failed
    :: (ND :<: sig, EffectCons m sig sigs sigl l) => m a
failed = logCall >> injectA Fail
{-# INLINE failed #-}

choose
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => [m a]
    -> m a
choose [] = failed
choose (p : ps) = foldr (?) p ps
{-# INLINE choose #-}

runND
    :: forall sig sigs sigl l a
     . Prog (Sig (ND :+: sig) sigs sigl l) a
    -> Prog (Sig sig sigs sigl (ListL l)) [a]
runND = unNDC . fold point con
{-# INLINE runND #-}

runNDSmart
    :: forall sig sigs sigl l a
     . SmartProg (Sig (ND :+: sig) sigs sigl l) a
    -> SmartProg (Sig sig sigs sigl (ListL l)) [a]
runNDSmart = unNDC . smartFold point con
{-# INLINE runNDSmart #-}

runNDC :: (EffectMonad m sig sigs sigl (ListL l)) => Cod (NDC m) a -> m [a]
runNDC = unNDC . runCod var
{-# INLINE runNDC #-}

algND :: (Monad m) => ND (m [a]) -> m [a]
algND Fail = return []
algND (Or l r) = (++) <$> l <*> r

instance Carrier NDC [] where
    cc = NDC
    unc = unNDC

instance LCarrier ListL [] where
    cl = ListL
    unl (ListL xs) = xs

instance GenForward NDC ListL where

instance (EffectMonad m sig sigs sigl (ListL l)) => TermAlgebra (NDC m) (Sig (ND :+: sig) sigs sigl l) where
    con s = case s of
        A (Algebraic op) -> NDC . (algND # (con . A . Algebraic)) . fmap unNDC $ op
        S op' -> sfwdg op'
        L op' -> lfwdg op'

    {-# INLINE con #-}
    var = cc'
    {-# INLINE var #-}

newtype NDC m a = NDC {unNDC :: m [a]}

instance (Functor m) => Functor (NDC m) where
    fmap f = NDC . fmap (fmap f) . unNDC
    {-# INLINE fmap #-}

instance (Monad m) => Pointed (NDC m) where
    point = NDC . return . return
    {-# INLINE point #-}

newtype ListL l a = ListL {unListL :: [l a]}
    deriving (Show)

instance (Functor l) => Functor (ListL l) where
    fmap f (ListL la) = ListL (fmap f <$> la)
    {-# INLINE fmap #-}

instance Lift ListL [] where
    lift = foldr (liftM2 (++)) (return [])
    lift2 =
        foldr
            (liftM2 (\xs ys -> ListL $ unListL xs ++ unListL ys))
            (return (ListL []))