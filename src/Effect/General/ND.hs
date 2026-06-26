{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}

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

import Effect.General.State (EffectCons, logPrimCall)
import Free
import GHC.Conc
import Signature
import Forwarding

data ND a = Fail | Or a a

instance Functor ND where
    fmap _ Fail = Fail
    fmap f (Or l r) = 
        let l' = f l
            r' = f r
         in r' `par` l' `pseq` Or l' r'
    {-# INLINE fmap #-}

(?)
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => m a
    -> m a
    -> m a
(?) p1 p2 = logPrimCall >> injectA (Or p1 p2)
{-# INLINE (?) #-}

failed
    :: (ND :<: sig, EffectCons m sig sigs sigl l) => m a
failed = logPrimCall >> injectA Fail
{-# INLINE failed #-}

choose
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => [m a]
    -> m a
choose [] = failed
choose (p : ps) = foldr (?) p ps
{-# INLINE choose #-}

runND
    :: (EffectMonad m sig sigs sigl (ListL l))
    => Prog (Sig (ND :+: sig) sigs sigl l) a
    -> m [a]
runND = unNDC . fold point con
{-# INLINE runND #-}

runNDSmart
    :: (EffectMonad m sig sigs sigl (ListL l))
    => SmartProg (Sig (ND :+: sig) sigs sigl l) a
    -> m [a]
runNDSmart = unNDC . smartFold point con
{-# INLINE runNDSmart #-}

runNDC :: (EffectMonad m sig sigs sigl (ListL l)) => Cod (NDC m) a -> m [a]
runNDC = unNDC . runCod var
{-# INLINE runNDC #-}

algND :: (Applicative m) => ND (m [a]) -> m [a]
algND Fail = pure []
algND (Or l r) = (++) <$> l <*> r

instance (EffectMonad m sig sigs sigl (ListL l)) => TermAlgebra (NDC m) (Sig (ND :+: sig) sigs sigl l) where
    con op = case op of
        A (Algebraic op') -> (wrap algND # (afwd . Algebraic)) op'
        S op' -> sfwd op'
        L op' -> lfwd op'
    {-# INLINE con #-}
    var = cc . point . point
    {-# INLINE var #-}

newtype NDC m a = NDC {unNDC :: m [a]} deriving (Functor)

instance LCarrier ListL [] where
    concatM [] = pure []
    concatM [x] = x
    concatM (x:xs) = liftA2 (++) x (concatM xs)

instance Carrier NDC []
instance Forward 'Outer NDC ListL

instance (Pointed m) => Pointed (NDC m) where
    point = NDC . point . point
    {-# INLINE point #-}

newtype ListL l a = ListL {unListL :: [l a]}
    deriving (Show, Functor)