{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Forwarding (
    Carrier (..),
    StateCarrier (..),
    ReaderCarrier (..),
    LCarrier (..),
    -- AForward(..),
    afwd,
    sfwd,
    lfwd,
    Forward,
    Strat (..),
    VoidL,
) where

import Control.Monad (join)
import Data.Coerce
import Data.Kind (Type)
import Free
import Signature
import Unsafe.Coerce (unsafeCoerce)

class Carrier c f | c -> f where
    cc :: m (f a) -> c m a
    default cc :: (Coercible (c m a) (m (f a))) => m (f a) -> c m a
    {-# INLINE cc #-}
    cc = coerce
    unc :: c m a -> m (f a)
    default unc :: (Coercible (m (f a)) (c m a)) => c m a -> m (f a)
    {-# INLINE unc #-}
    unc = coerce
    wrap :: (Functor eff) => (eff (m (f a)) -> m (f a)) -> eff (c m a) -> c m a
    wrap alg = cc . alg . fmap unc

class StateCarrier c s | c -> s where
    ccst :: (s -> m (s, a)) -> c m a
    default ccst :: (Coercible (c m a) (s -> m (s, a))) => (s -> m (s, a)) -> c m a
    {-# INLINE ccst #-}
    ccst = coerce
    uncst :: c m a -> (s -> m (s, a))
    default uncst :: (Coercible (s -> m (s, a)) (c m a)) => c m a -> (s -> m (s, a))
    {-# INLINE uncst #-}
    uncst = coerce
    wrapst :: (Functor eff) => (eff (s -> m (s, a)) -> s -> m (s, a)) -> eff (c m a) -> c m a
    wrapst alg = ccst . alg . fmap uncst

class ReaderCarrier c r | c -> r where
    ccr :: (r -> m a) -> c m a
    default ccr :: (Coercible (c m a) (r -> m a)) => (r -> m a) -> c m a
    {-# INLINE ccr #-}
    ccr = coerce
    uncr :: c m a -> (r -> m a)
    default uncr :: (Coercible (r -> m a) (c m a)) => c m a -> (r -> m a)
    {-# INLINE uncr #-}
    uncr = coerce
    wrapr :: (Functor eff) => (eff (r -> m a) -> r -> m a) -> eff (c m a) -> c m a
    wrapr alg = ccr . alg . fmap uncr

class LCarrier cL f | cL -> f where
    cl :: f (l x) -> cL l x
    default cl :: (Coercible (cL l x) (f (l x))) => f (l x) -> cL l x
    {-# INLINE cl #-}
    cl = coerce
    unl :: cL l x -> f (l x)
    default unl :: (Coercible (f (l x)) (cL l x)) => cL l x -> f (l x)
    {-# INLINE unl #-}
    unl = coerce

    concatM
        :: (TermMonad m (Sig sig sigs sigl (cL l)))
        => f (m (f a))
        -> m (f a)
    default concatM
        :: (TermMonad m (Sig sig sigs sigl (cL l)), Traversable f, Monad f)
        => f (m (f a))
        -> m (f a)
    {-# INLINE concatM #-}
    concatM = fmap join . sequence

{-# RULES "fmapcc/coerce" fmap coerce = unsafeCoerce #-}

type family StratApply (strat :: Strat) (l :: Type -> Type) (ll :: (Type -> Type) -> Type -> Type) :: Type -> Type where
    StratApply 'Outer l ll = ll l
    StratApply 'Reader l ll = l
    StratApply 'State l ll = ll l

data Strat = Outer | Reader | State

class (DerivingStrat strat c ll) => Forward (strat :: Strat) c ll | c -> strat ll

class DerivingStrat strat c ll where
    dafwd
        :: (TermMonad m (Sig sig sigs sigl (StratApply strat l ll)))
        => Algebraic sig (c m) (c m a) -> c m a
    dsfwd
        :: (TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Pointed m, Functor (c m), Applicative m)
        => Scoped sigs (c m) (c m a) -> c m a
    dlfwd
        :: (TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Pointed m, Applicative m)
        => Latent sigl l (c m) (c m a) -> c m a

afwd
    :: forall ll strat sig sigs sigl l c m a
     . (Forward strat c ll, TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Applicative m)
    => Algebraic sig (c m) (c m a) -> c m a
afwd = dafwd @strat @_ @ll @_ @_ @_ @_ @l

sfwd
    :: forall ll strat sig sigs sigl l c m a
     . (Forward strat c ll, TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Applicative m, Pointed m, Functor (c m))
    => Scoped sigs (c m) (c m a) -> c m a
sfwd = dsfwd @strat @_ @ll @_ @_ @_ @_ @l

lfwd
    :: forall ll strat sig sigs sigl l c m a
     . (Forward strat c ll, TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Pointed m, Applicative m)
    => Latent sigl l (c m) (c m a) -> c m a
lfwd = dlfwd @strat @_ @ll @_ @_ @_ @_ @l

instance (Carrier c f, LCarrier ll f, Pointed f) => DerivingStrat 'Outer c ll where
    dafwd (Algebraic op) = cc . con . A . Algebraic . fmap unc $ op
    dsfwd (Enter op) = cc . con . S . Enter . fmap (fmap (concatM @ll) . unc . fmap unc) $ op
    dlfwd (Node op l st k) = cc $ con $ L $ Node op (cl $ point l) (st' st) k'
      where
        st' st2 c l' = cl <$> concatM (fmap (unc . st2 c) (unl l'))
        k' = concatM . fmap (unc . k) . unl

instance (StateCarrier c s, LCarrier ll ((,) s)) => DerivingStrat 'State c ll where
    dafwd (Algebraic op) = ccst $ \s -> con $ A $ Algebraic $ fmap (`uncst` s) op
    dsfwd (Enter op) = ccst $ \s -> con $ S $ Enter $ fmap (go s) op
      where
        go s hhx = fmap (\(s', hhx') -> uncst hhx' s') (uncst hhx s)
    dlfwd (Node op l st k) = ccst $
        \s -> con $ L $ Node op (cl (s, l)) (st' st) k'
      where
        st' st2 c stl = let (s', lv) = unl stl in cl <$> uncst (st2 c lv) s'
        k' stl = let (s', lv) = unl stl in uncst (k lv) s'

instance (ReaderCarrier c r) => DerivingStrat 'Reader c ll where
    dafwd (Algebraic op) = ccr $ \r -> con $ A $ Algebraic $ fmap (`uncr` r) op
    dsfwd (Enter op) = ccr $ \r -> con $ S $ Enter $ fmap (go r) op
      where
        go r hhx = fmap (`uncr` r) (uncr hhx r)
    dlfwd (Node op l st k) = ccr $ \r -> con $ L $ Node op l (\c lv -> uncr (st c lv) r) (\lv -> uncr (k lv) r)

data VoidL (l :: Type -> Type) a
