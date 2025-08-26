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
    Union,
    absurd,
    (:.:),
    prj3,
    HasCallStack,
    OuterCarrier (..),
    StateCarrier (..),
    ReaderCarrier (..),
    LCarrier (..),
    -- AForward(..),
    afwd,
    sfwd,
    lfwd,
    DeriveForward (..),
    CarrierDerivingStrat (..),
    VoidL,
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

deriving instance Functor (Latent sig l f)

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
  deriving (Functor)

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

class OuterCarrier c f | c -> f where
    cc :: m (f a) -> c m a
    default cc :: (Coercible (c m a) (m (f a))) => m (f a) -> c m a
    cc = coerce
    unc :: c m a -> m (f a)
    default unc :: (Coercible (m (f a)) (c m a)) => c m a -> m (f a)
    unc = coerce
    wrap :: (Functor eff) => (eff (m (f a)) -> m (f a)) -> eff (c m a) -> c m a
    wrap alg = cc . alg . fmap unc

class StateCarrier c s | c -> s where
    ccst :: (s -> m (s, a)) -> c m a
    default ccst :: (Coercible (c m a) (s -> m (s, a))) => (s -> m (s, a)) -> c m a
    ccst = coerce
    uncst :: c m a -> (s -> m (s, a))
    default uncst :: (Coercible (s -> m (s, a)) (c m a)) => c m a -> (s -> m (s, a))
    uncst = coerce
    wrapst :: (Functor eff) => (eff (s -> m (s, a)) -> s -> m (s, a)) -> eff (c m a) -> c m a
    wrapst alg = ccst . alg . fmap uncst

class ReaderCarrier c r | c -> r where
    ccr :: (r -> m a) -> c m a
    default ccr :: (Coercible (c m a) (r -> m a)) => (r -> m a) -> c m a
    ccr = coerce
    uncr :: c m a -> (r -> m a)
    default uncr :: (Coercible (r -> m a) (c m a)) => c m a -> (r -> m a)
    uncr = coerce
    wrapr :: (Functor eff) => (eff (r -> m a) -> r -> m a) -> eff (c m a) -> c m a
    wrapr alg = ccr . alg . fmap uncr

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

    lift2
        :: (TermAlgebra m (Sig sig sigs sigl (cL l)), Applicative m)
        => f (m (cL l x))
        -> m (cL l x)

----
type family Test (strat :: CarrierDerivingStrat) (l :: Type -> Type) (ll :: (Type -> Type) -> Type -> Type) :: Type -> Type where
    Test 'Outer l ll = ll l
    Test 'Reader l ll = l
    Test 'State l ll = ll l

data CarrierDerivingStrat = Outer | Reader | State

class (DerivingStrat strat c ll) => DeriveForward (strat :: CarrierDerivingStrat) c ll | c -> strat

class DerivingStrat strat c ll where
    dafwd
        :: (TermAlgebra m (Sig sig sigs sigl (Test strat l ll)))
        => Algebraic sig (c m) (c m a) -> c m a
    dsfwd
        :: (TermAlgebra m (Sig sig sigs sigl (Test strat l ll)), Pointed m, Functor (c m), Applicative m)
        => Scoped sigs (c m) (c m a) -> c m a
    dlfwd
        :: (TermAlgebra m (Sig sig sigs sigl (Test strat l ll)), Pointed m, Applicative m)
        => Latent sigl l (c m) (c m a) -> c m a

afwd
    :: forall ll strat sig sigs sigl l c m a
     . (DeriveForward strat c ll, TermAlgebra m (Sig sig sigs sigl (Test strat l ll)), Applicative m)
    => Algebraic sig (c m) (c m a) -> c m a
afwd = dafwd @strat @_ @ll @_ @_ @_ @_ @l

sfwd
    :: forall ll strat sig sigs sigl l c m a
     . (DeriveForward strat c ll, TermAlgebra m (Sig sig sigs sigl (Test strat l ll)), Applicative m, Pointed m, Functor (c m))
    => Scoped sigs (c m) (c m a) -> c m a
sfwd = dsfwd @strat @_ @ll @_ @_ @_ @_ @l

lfwd
    :: forall ll strat sig sigs sigl l c m a
     . (DeriveForward strat c ll, TermAlgebra m (Sig sig sigs sigl (Test strat l ll)), Pointed m, Applicative m)
    => Latent sigl l (c m) (c m a) -> c m a
lfwd = dlfwd @strat @_ @ll @_ @_ @_ @_ @l

instance (OuterCarrier c f, LCarrier ll f, Pointed f) => DerivingStrat 'Outer c ll where
    dafwd (Algebraic op) = cc . con . A . Algebraic . fmap unc $ op
    dsfwd (Enter op) = cc . con . S . Enter . fmap (fmap (lift @ll) . unc . fmap unc) $ op
    dlfwd (Node op l st k) = cc $ con $ L $ Node op (cl $ point l) (st' st) k'
      where
        st' st2 c l' = lift2 (fmap (\x -> cl <$> unc (st2 c x)) (unl l'))
        k' = lift . fmap (unc . k) . unl

instance (StateCarrier c s, LCarrier ll ((,) s)) => DerivingStrat 'State c ll where
    dafwd (Algebraic op) = ccst $ \s -> con $ A $ Algebraic $ fmap (`uncst` s) op
    dsfwd (Enter op) = ccst $ \s -> con $ S $ Enter $ fmap (go s) op
      where
        go s hhx = fmap (\(s', hhx') -> uncst hhx' s') (uncst hhx s)
    dlfwd (Node op l st k) = ccst $
        \s -> con $ L $ Node op (cl (s, l)) (st' st) k'
      where
        st' st c stl = let (s', lv) = unl stl in cl <$> uncst (st c lv) s'
        k' stl = let (s', lv) = unl stl in uncst (k lv) s'

instance (ReaderCarrier c r) => DerivingStrat 'Reader c ll where
    dafwd (Algebraic op) = ccr $ \r -> con $ A $ Algebraic $ fmap (`uncr` r) op
    dsfwd (Enter op) = ccr $ \r -> con $ S $ Enter $ fmap (go r) op
      where
        go r hhx = fmap (`uncr` r) (uncr hhx r)
    dlfwd (Node op l st k) = ccr $ \r -> con $ L $ Node op l (\c lv -> uncr (st c lv) r) (\lv -> uncr (k lv) r)

data VoidL (l :: Type -> Type) a