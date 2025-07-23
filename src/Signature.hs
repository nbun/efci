{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
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

module Signature (
    (:+:),
    (:<:),
    HFunctor,
    NoSub,
    Sig (..),
    (:+++:) (..),
    EffectMonad,
    Algebraic (..),
    Scoped (..),
    Latent (..),
    Id (..),
    (:<<<<:),
    injectA,
    injectS,
    injectL,
    (#),
    OneSub (..),
    LVoid,
    (:<<<:),
    injV,
    Union,
    absurd,
    (:.:),
    prj3,
    HasCallStack,
    OuterCarrier (..),
    StateCarrier (..),
    InnerCarrier (..),
    LCarrier (..),
    -- AForward(..),
    AForwardNoL (..),
    SForwardNoL (..),
    LForwardNoL (..),
    InnerCarrier (..),
    Forward (..),
    DeriveForward (..),
    CarrierDerivingStrat (..),
) where

import Data.Coerce
import Data.Kind (Type)
import Data.Union
import Free
import GHC.Base (Constraint, MonadPlus (..))
import GHC.Stack (HasCallStack)

type (:<:) e r = Elem e r

type (:+:) e r = (e ': r)

infixr 0 :+:

data ((sig1 :: Type -> (Type -> Type) -> Type) :+++: sig2) p c
    = Inl3 (sig1 p c)
    | Inr3 (sig2 p c)

data HVoid (f :: Type -> Type) a deriving (Functor)

runHVoid :: Prog HVoid a -> a
runHVoid (Return x) = x
runHVoid (Call op) = case op of {}

instance HFunctor HVoid where
    hmap f x = case x of {}

type family (:.:) effs sig :: Constraint where
    '[] :.: sig = ()
    (x ': xs) :.: sig = (x :<: sig, xs :.: sig)

class v1 :<<<: v2 where
    injV :: v1 -> v2
    projV :: v2 -> Maybe v1

instance (a :<<<: a) where
    injV = id
    projV = Just

newtype Id a = Id {unId :: a} deriving (Functor, Show)

instance Pointed Id where
    point = Id
    {-# INLINE point #-}

instance Applicative Id where
    Id f <*> Id x = Id (f x)
    pure = Id

newtype Algebraic sig (f :: Type -> Type) a = Algebraic (Union sig a) deriving (Functor)

instance HFunctor (Algebraic sig) where
    hmap _ (Algebraic op) = Algebraic op
    {-# INLINE hmap #-}

newtype Scoped sig f a where
    Enter :: Union sig (f a) -> Scoped sig f a
    deriving (Functor)

instance HFunctor (Scoped sig) where
    hmap k (Enter sc) = Enter (fmap k sc)
    {-# INLINE hmap #-}

data Latent sig l f a where
    Node :: sig p c -> l () -> (forall x. c x -> l () -> f (l x)) -> (l p -> a) -> Latent sig l f a

instance Functor (Latent sig l f) where
    fmap f (Node sub l st c) = Node sub l st (f . c)

instance HFunctor (Latent sig l) where
    hmap k (Node sub l st c) = Node sub l (fmap k . st) c
    {-# INLINE hmap #-}

data NoSub :: Type -> Type

data OneSub v :: Type -> Type where
    One :: OneSub v v

class (sub :: Type -> (Type -> Type) -> Type) :<<<<: sup where
    inj3 :: sub p c -> sup p c
    prj3 :: sup p c -> Maybe (sub p c)

instance {-# OVERLAPPING #-} sig1 :<<<<: (sig1 :+++: sig2) where
    inj3 = Inl3
    prj3 (Inl3 sig) = Just sig
    prj3 _ = Nothing

instance {-# OVERLAPPABLE #-} (sig :<<<<: sig2) => sig :<<<<: (sig1 :+++: sig2) where
    inj3 = Inr3 . inj3
    prj3 (Inr3 sig) = prj3 sig
    prj3 _ = Nothing

data LVoid p c deriving (Functor)

data Sig sig sigs sigl l f a = A (Algebraic sig f a) | S (Scoped sigs f a) | L (Latent sigl l f a)

instance (Functor f) => Functor (Sig sig sigs sigl l f) where
    fmap f (A !a) = A (fmap f a)
    fmap f (S !s) = S (fmap f s)
    fmap f (L !l) = L (fmap f l)

injectS :: forall sig sigs sigl l m a eff. (eff :<: sigs, TermMonad m (Sig sig sigs sigl l), Functor eff) => eff (m (m a)) -> m a
injectS = con . S . Enter . inj
{-# INLINE injectS #-}

injectA
    :: (eff :<: sig, TermMonad m (Sig sig sigs sigl l), Functor eff)
    => eff (m a)
    -> m a
injectA e = con (A (Algebraic (inj e)))
{-# INLINE injectA #-}

injectL
    :: (eff :<<<<: sigl, TermMonad m (Sig sig sigs sigl l))
    => eff p c
    -> l ()
    -> ( forall x
          . c x
         -> l ()
         -> m (l x)
       )
    -> ( l p
         -> m a
       )
    -> m a
injectL op l st k = con $ L $ Node (inj3 op) l st k
{-# INLINE injectL #-}

instance HFunctor (Sig sig sigs sigl l) where
    hmap f (A a) = A (hmap f a)
    hmap f (S s) = S (hmap f s)
    hmap f (L l) = L (hmap f l)
    {-# INLINE hmap #-}

type EffectMonad m sig sigs sigl l = (TermMonad m (Sig sig sigs sigl l))

-- {-# RULES "fmapCoerce/coerce" fmap coerce = unsafeCoerce #-}

-- conA
--     :: (EffectMonad m sig sigs sigl (ll l), Lift ll f, Functor (c m), Carrier c f, LCarrier ll f)
--     => (eff (m (f a)) -> m (f a)) -> Sig (eff :+: sig) sigs sigl l (c m) (c m a) -> c m a
-- conA alg eff = case eff of
--     A (Algebraic op) -> cc . (alg # afwd) . fmap unc $ op
--       where
--         afwd = con . A . Algebraic
--     S (Enter op) -> cc . con . S . Enter . fmap (fmap lift . unc . fmap unc) $ op
--     L (Node op l st k) -> cc $ con $ L $ Node op (cl' l) (st' st) k'
--       where
--         st' st2 c l' = lift2 (fmap (\x -> cl <$> unc (st2 c x)) (unl l'))
--         k' = lift . fmap (unc . k) . unl

-- conA
--     :: (EffectMonad m sig sigs sigl (ll l), Lift ll f, Functor (c m), OuterCarrier c f, LCarrier ll f)
--     => (eff (m (f a)) -> m (f a)) -> Sig (eff :+: sig) sigs sigl l (c m) (c m a) -> c m a
-- conA alg eff = case eff of
--     A (Algebraic op) -> cc . (alg # afwd) . fmap unc $ op
--       where
--         afwd = con . A . Algebraic
--     S (Enter op) -> cc . con . S . Enter . fmap (fmap lift . unc . fmap unc) $ op
--     L (Node op l st k) -> cc $ con $ L $ Node op (cl' l) (st' st) k'
--       where
--         st' st2 c l' = lift2 (fmap (\x -> cl <$> unc (st2 c x)) (unl l'))
--         k' = lift . fmap (unc . k) . unl

-- conA
-- :: (EffectMonad m sig sigs sigl (ll l), Lift ll f, Functor (c m), Carrier c f, LCarrier ll f)
-- => (eff (m (f a)) -> m (f a)) -> Sig (eff :+: sig) sigs sigl l (c m) (c m a) -> c m a
-- conA'
--     :: (EffectMonad m sig sigs sigl (cL l), Lift cL f, Functor (c m), Functor f)
--     => (m (f a) -> c m a)
--     -> (forall x. c m x -> m (f x))
--     -> (forall x. f (l x) -> cL l x)
--     -> (forall x. l x -> cL l x)
--     -> (forall x. cL l x -> f (l x))
--     -> (eff (m (f a)) -> m (f a))
--     -> Sig (eff :+: sig) sigs sigl l (c m) (c m a)
--     -> c m a
-- conA' cc unc cl cl' unl alg eff = case eff of
--     A (Algebraic op) -> cc . (alg # afwd) . fmap unc $ op
--       where
--         afwd = con . A . Algebraic
--     S (Enter op) -> cc . con . S . Enter . fmap (fmap lift . unc . fmap unc) $ op
--     L (Node op l st k) -> cc $ con $ L $ Node op (cl' l) (\c l' -> lift2 (fmap (\x -> cl <$> unc (st c x)) (unl l'))) k'
--       where
--         k' = lift . fmap (unc . k) . unl

class OuterCarrier c f | c -> f where
    cc :: m (f a) -> c m a
    default cc :: (Coercible (c m a) (m (f a))) => m (f a) -> c m a
    cc = coerce
    unc :: c m a -> m (f a)
    default unc :: (Coercible (m (f a)) (c m a)) => c m a -> m (f a)
    unc = coerce

class InnerCarrier c f | c -> f where
    cci :: f (m a) -> c m a
    default cci :: (Coercible (c m a) (f (m a))) => f (m a) -> c m a
    cci = coerce
    unci :: c m a -> f (m a)
    default unci :: (Coercible (f (m a)) (c m a)) => c m a -> f (m a)
    unci = coerce
    f2m :: f (m a) -> m a
    m2f :: m a -> f (m a)

class StateCarrier c s | c -> s where
    ccst :: (s -> m (s, a)) -> c m a
    default ccst :: (Coercible (c m a) (s -> m (s, a))) => (s -> m (s, a)) -> c m a
    ccst = coerce
    uncst :: c m a -> (s -> m (s, a))
    default uncst :: (Coercible (s -> m (s, a)) (c m a)) => c m a -> (s -> m (s, a))
    uncst = coerce

class LCarrier cL f | cL -> f where
    cl :: f (l x) -> cL l x
    default cl :: (Coercible (cL l x) (f (l x))) => f (l x) -> cL l x
    cl = coerce
    unl :: cL l x -> f (l x)
    default unl :: (Coercible (f (l x)) (cL l x)) => cL l x -> f (l x)
    unl = coerce

    lift
        :: (TermAlgebra m (Sig sig sigs sigl (cL l)), Applicative m)
        => f (m (f a))
        -> m (f a)
    -- lift = foldr (liftA2 mplus) (pure mzero)

    lift2
        :: (TermAlgebra m (Sig sig sigs sigl (cL l)), Applicative m)
        => f (m (cL l x))
        -> m (cL l x)

class SForwardNoL c where
    sfwdnl :: (TermAlgebra m (Sig sig sigs sigl l), Monad m, Pointed m) => Scoped sigs (c m) (c m a) -> c m a

class LForwardNoL c where
    lfwdnl :: (TermAlgebra m (Sig sig sigs sigl l), Monad m, Pointed m) => Latent sigl l (c m) (c m a) -> c m a

----

data CarrierDerivingStrat = Outer | Inner | State

-- AForward

class (DerivingStrat strat c ll) => DeriveForward (strat :: CarrierDerivingStrat) c ll | c -> strat

class DerivingStrat strat c ll where
    dafwd
        :: (TermAlgebra m (Sig sig sigs sigl (ll l)))
        => Algebraic sig (c m) (c m a) -> c m a
    dsfwd
        :: (TermAlgebra m (Sig sig sigs sigl (ll l)), Pointed m, Functor (c m), Applicative m)
        => Scoped sigs (c m) (c m a) -> c m a
    dlfwd
        :: (TermAlgebra m (Sig sig sigs sigl (ll l)), Pointed m, Applicative m)
        => Latent sigl l (c m) (c m a) -> c m a

class Forward c ll | c -> ll where
    afwd
        :: (TermAlgebra m (Sig sig sigs sigl (ll l)), Applicative m)
        => Algebraic sig (c m) (c m a) -> c m a
    default afwd
        :: forall strat sig sigs sigl l m a
         . (DeriveForward strat c ll, TermAlgebra m (Sig sig sigs sigl (ll l)), Applicative m)
        => Algebraic sig (c m) (c m a) -> c m a
    afwd = dafwd @strat

    sfwd
        :: (TermAlgebra m (Sig sig sigs sigl (ll l)), Pointed m, Applicative m)
        => Scoped sigs (c m) (c m a) -> c m a
    default sfwd
        :: forall strat sig sigs sigl l m a
         . (DeriveForward strat c ll, TermAlgebra m (Sig sig sigs sigl (ll l)), Applicative m, Pointed m, Functor (c m))
        => Scoped sigs (c m) (c m a) -> c m a
    sfwd = dsfwd @strat

    lfwd
        :: (TermAlgebra m (Sig sig sigs sigl (ll l)), Pointed m, Applicative m)
        => Latent sigl l (c m) (c m a) -> c m a
    default lfwd
        :: forall strat sig sigs sigl l m a
         . (DeriveForward strat c ll, TermAlgebra m (Sig sig sigs sigl (ll l)), Pointed m, Applicative m)
        => Latent sigl l (c m) (c m a) -> c m a
    lfwd = dlfwd @strat

instance (OuterCarrier c f, LCarrier ll f, Pointed f) => DerivingStrat 'Outer c ll where
    dafwd (Algebraic op) = cc . con . A . Algebraic . fmap unc $ op
    dsfwd (Enter op) = cc . con . S . Enter . fmap (fmap (lift @ll) . unc . fmap unc) $ op
    dlfwd (Node op l st k) = cc $ con $ L $ Node op (cl $ point l) (st' st) k'
      where
        st' st2 c l' = lift2 (fmap (\x -> cl <$> unc (st2 c x)) (unl l'))
        k' = lift . fmap (unc . k) . unl

instance (InnerCarrier c f) => DerivingStrat 'Inner c ll where
    dafwd (Algebraic op) = cci . m2f @c . con . A . Algebraic . fmap (f2m @c . unci) $ op

-- dsfwd (Enter op) = cci . m2f @c . con . S . Enter . fmap (fmap lift . f2m @c . unci . fmap (f2m @c . unci)) $ op
-- dlfwd (Node op l st k) = cci $ m2f @c $ con $ L $ Node op (cl' l) (st' st) k'
--   where
--     st' st2 c l' = lift2 (fmap (\x -> cl <$> f2m @c (unci (st2 c x))) (unl l'))
--     k' = lift . fmap (f2m @c . unci . k) . unl

instance (StateCarrier c s, LCarrier ll ((,) s)) => DerivingStrat 'State c ll where
    dafwd (Algebraic op) = ccst $ \s -> con $ A $ Algebraic $ fmap (\x -> uncst x s) op
    dsfwd (Enter op) = ccst $ \s -> con $ S $ Enter $ fmap (go s) op
      where
        go s = \hhx -> fmap (\(s', hhx') -> uncst hhx' s') (uncst hhx s)
    dlfwd (Node op l st k) = ccst $
        \s -> con $ L $ Node op (cl (s, l)) (st' st) k'
      where
        st' st c stl = let (s', lv) = unl stl in cl <$> uncst (st c lv) s'
        k' stl = let (s', lv) = unl stl in uncst (k lv) s'

class AForwardNoL c where
    afwdnl :: (TermAlgebra m (Sig sig sigs sigl l)) => Algebraic sig (c m) (c m a) -> c m a
