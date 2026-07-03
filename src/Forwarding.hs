{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- | Effect forwarding infrastructure

This module provides type classes and utilities for forwarding effects
through different carrier types and using different strategies. It supports:

* Carrier classes
* Forwarding strategies (Default, Reader, State)
* Strategy-polymorphic forwarding functions
-}
module Forwarding (
    Carrier (..),
    StateCarrier (..),
    ReaderCarrier (..),
    LCarrier (..),
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

{- | Carrier newtype class

Provides operations for wrapping and unwrapping effectful computations
in a carrier newtype @c@.
-}
class Carrier c f | c -> f where
    -- | Wrap a computation in the carrier newtype
    cc :: m (f a) -> c m a
    default cc :: (Coercible (c m a) (m (f a))) => m (f a) -> c m a
    {-# INLINE cc #-}
    cc = coerce

    -- | Unwrap a carrier newtype to get the underlying effectful computation
    unc :: c m a -> m (f a)
    default unc :: (Coercible (m (f a)) (c m a)) => c m a -> m (f a)
    {-# INLINE unc #-}
    unc = coerce

    -- | Allows an @eff@ algebra to work on a carrier newtype
    wrap :: (Functor eff) => (eff (m (f a)) -> m (f a)) -> eff (c m a) -> c m a
    wrap alg = cc . alg . fmap unc

-- | Carrier class for state effects
class StateCarrier c s | c -> s where
    -- | Wrap a stateful computation in the carrier newtype
    ccst :: (s -> m (s, a)) -> c m a
    default ccst :: (Coercible (c m a) (s -> m (s, a))) => (s -> m (s, a)) -> c m a
    {-# INLINE ccst #-}
    ccst = coerce

    -- | Unwrap a state carrier newtype to get the underlying stateful computation
    uncst :: c m a -> (s -> m (s, a))
    default uncst :: (Coercible (s -> m (s, a)) (c m a)) => c m a -> (s -> m (s, a))
    {-# INLINE uncst #-}
    uncst = coerce

    -- | Allows an @eff@ algebra to work on a carrier newtype
    wrapst :: (Functor eff) => (eff (s -> m (s, a)) -> s -> m (s, a)) -> eff (c m a) -> c m a
    wrapst alg = ccst . alg . fmap uncst

-- | Carrier class for reader effects
class ReaderCarrier c r | c -> r where
    -- | Wrap a reader computation in the carrier newtype
    ccr :: (r -> m a) -> c m a
    default ccr :: (Coercible (c m a) (r -> m a)) => (r -> m a) -> c m a
    {-# INLINE ccr #-}
    ccr = coerce

    -- | Unwrap a reader carrier newtype to get the underlying reader computation
    uncr :: c m a -> (r -> m a)
    default uncr :: (Coercible (r -> m a) (c m a)) => c m a -> (r -> m a)
    {-# INLINE uncr #-}
    uncr = coerce

    -- | Allows an @eff@ algebra to work on a carrier newtype
    wrapr :: (Functor eff) => (eff (r -> m a) -> r -> m a) -> eff (c m a) -> c m a
    wrapr alg = ccr . alg . fmap uncr

-- | Latent carrier newtype class
class LCarrier cL f | cL -> f where
    -- | Wrap a carrier value in the carrier newtype
    cl :: f (l x) -> cL l x
    default cl :: (Coercible (cL l x) (f (l x))) => f (l x) -> cL l x
    {-# INLINE cl #-}
    cl = coerce

    -- | Unwrap a latent carrier newtype to get the underlying carrier value
    unl :: cL l x -> f (l x)
    default unl :: (Coercible (f (l x)) (cL l x)) => cL l x -> f (l x)
    {-# INLINE unl #-}
    unl = coerce

    {- | Monadic concatenation of carrier-effect nestings.

    Default implementation uses 'sequence' and 'join' to flatten the structure,
    which can sometimes be much slower than a specialized implementation. For this
    reason, the function is provided as part of the class.
    -}
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

{- | Controversial rewrite rule that prevents redundant structure traversals

Only holds as long as all involved functor instances are lawful,
see https://oleg.fi/gists/posts/2019-07-31-fmap-coerce-coerce.html for details.
-}
{-# RULES "fmapcc/coerce" fmap coerce = unsafeCoerce #-}

{- | Type family for applying strategies to latent carriers

Determines how the latent carrier @l@ is applied based on the strategy
-}
type family StratApply (strat :: Strat) (l :: Type -> Type) (ll :: (Type -> Type) -> Type -> Type) :: Type -> Type where
    StratApply 'Default l ll = ll l
    StratApply 'Reader l ll = l
    StratApply 'State l ll = ll l

{- | Forwarding strategies for effect handling

* 'Default': For effects that express their semantics through extending the result parameter
* 'Reader': For reader effects
* 'State': For stateful effects
-}
data Strat = Default | Reader | State

{- | Main forwarding class

Associates the carrier @c@ with the strategy @strat@.
As there are no methods to implement, instances require only the instance head.
-}
class (DerivingStrat strat c ll) => Forward (strat :: Strat) c ll | c -> strat ll

{- | Class for deriving forwarding strategy implementations

Provides the actual implementations for forwarding algebraic, scoped, and latent effects.
-}
class DerivingStrat strat c ll where
    -- | Forward an algebraic effect using the strategy @strat@
    dafwd
        :: (TermMonad m (Sig sig sigs sigl (StratApply strat l ll)))
        => Algebraic sig (c m) (c m a) -> c m a

    -- | Forward a scoped effect using the strategy @strat@
    dsfwd
        :: (TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Pointed m, Functor (c m), Applicative m)
        => Scoped sigs (c m) (c m a) -> c m a

    -- | Forward a latent effect using the strategy @strat@
    dlfwd
        :: (TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Pointed m, Applicative m)
        => Latent sigl l (c m) (c m a) -> c m a

-- | Forwarding function for algebraic effects that selects the strategy based on the 'Forward' constraint.
afwd
    :: forall ll strat sig sigs sigl l c m a
     . (Forward strat c ll, TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Applicative m)
    => Algebraic sig (c m) (c m a) -> c m a
afwd = dafwd @strat @_ @ll @_ @_ @_ @_ @l

-- | Forwarding function for scoped effects that selects the strategy based on the 'Forward' constraint.
sfwd
    :: forall ll strat sig sigs sigl l c m a
     . (Forward strat c ll, TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Applicative m, Pointed m, Functor (c m))
    => Scoped sigs (c m) (c m a) -> c m a
sfwd = dsfwd @strat @_ @ll @_ @_ @_ @_ @l

-- | Forwarding function for latent effects that selects the strategy based on the 'Forward' constraint.
lfwd
    :: forall ll strat sig sigs sigl l c m a
     . (Forward strat c ll, TermMonad m (Sig sig sigs sigl (StratApply strat l ll)), Pointed m, Applicative m)
    => Latent sigl l (c m) (c m a) -> c m a
lfwd = dlfwd @strat @_ @ll @_ @_ @_ @_ @l

{- | Default forwarding strategy instance

Forwards effects using a default strategy.
-}
instance (Carrier c f, LCarrier ll f, Pointed f) => DerivingStrat 'Default c ll where
    -- Forward algebraic effects by wrapping in carrier and applying the algebra
    dafwd (Algebraic op) = cc . con . A . Algebraic . fmap unc $ op

    -- Forward scoped effects by wrapping in carrier and handling the continuations
    dsfwd (Enter op) = cc . con . S . Enter . fmap (fmap (concatM @ll) . unc . fmap unc) $ op

    -- Forward latent effects by wrapping in carrier and handling the nodes
    dlfwd (Node op l st k) = cc $ con $ L $ Node op (cl $ point l) (st' st) k'
      where
        st' st2 c l' = cl <$> concatM (fmap (unc . st2 c) (unl l'))
        k' = concatM . fmap (unc . k) . unl

{- | State forwarding strategy instance

Forwards effects using a state-specific strategy.
-}
instance (StateCarrier c s, LCarrier ll ((,) s)) => DerivingStrat 'State c ll where
    -- Forward algebraic effects by running with initial state
    dafwd (Algebraic op) = ccst $ \s -> con $ A $ Algebraic $ fmap (`uncst` s) op

    -- Forward scoped effects by running with initial state and threading state
    dsfwd (Enter op) = ccst $ \s -> con $ S $ Enter $ fmap (go s) op
      where
        go s hhx = fmap (\(s', hhx') -> uncst hhx' s') (uncst hhx s)

    -- Forward latent effects by running with initial state and threading state
    dlfwd (Node op l st k) = ccst $
        \s -> con $ L $ Node op (cl (s, l)) (st' st) k'
      where
        st' st2 c stl = let (s', lv) = unl stl in cl <$> uncst (st2 c lv) s'
        k' stl = let (s', lv) = unl stl in uncst (k lv) s'

{- | Reader forwarding strategy instance

Forwards effects using a reader-specific strategy.
-}
instance (ReaderCarrier c r) => DerivingStrat 'Reader c ll where
    -- Forward algebraic effects by running with reader context
    dafwd (Algebraic op) = ccr $ \r -> con $ A $ Algebraic $ fmap (`uncr` r) op

    -- Forward scoped effects by running with reader context
    dsfwd (Enter op) = ccr $ \r -> con $ S $ Enter $ fmap (go r) op
      where
        go r hhx = fmap (`uncr` r) (uncr hhx r)

    -- Forward latent effects by running with reader context
    dlfwd (Node op l st k) = ccr $ \r -> con $ L $ Node op l (\c lv -> uncr (st c lv) r) (\lv -> uncr (k lv) r)

-- | Empty latent carrier
data VoidL (l :: Type -> Type) a
