{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- |
Effect signatures

This module provides the foundational type-level infrastructure for building
signature types and injecting/projecting values w.r.t. a specific signature.
-}
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
    (:<<:),
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
    absurdNoSub,
) where

import Data.Kind (Type)
import Data.Union
import Free
import GHC.Base (Constraint)
import GHC.Stack (HasCallStack)

-- | Type operator synonym for membership in an effect signature
type (:<:) e r = Elem e r

-- | Type-level operator for prepending an effect to a signature
type (:+:) e r = (e ': r)

infixr 0 :+:

-- | Type family for expressing that all effects in a list are members of a signature
type family (:.:) effs sig :: Constraint where
    '[] :.: sig = ()
    (x ': xs) :.: sig = (x :<: sig, xs :.: sig)

-- | Identity monad
newtype Id a = Id {unId :: a} deriving (Functor, Show)

instance Pointed Id where
    point = Id
    {-# INLINE point #-}

instance Applicative Id where
    Id f <*> Id x = Id (f x)
    pure = Id

-- | Adapter for algebraic effects
newtype Algebraic sig (f :: Type -> Type) a = Algebraic (Union sig a) deriving (Functor)

instance HFunctor (Algebraic sig) where
    hmap _ (Algebraic op) = Algebraic op
    {-# INLINE hmap #-}

-- | Adapter for scoped effects
newtype Scoped sig f a where
    Enter :: Union sig (f a) -> Scoped sig f a
    deriving (Functor)

instance HFunctor (Scoped sig) where
    hmap k (Enter sc) = Enter (fmap k sc)
    {-# INLINE hmap #-}

-- | Adapter for latent effects
data Latent sig l f a where
    Node :: sig p c -> l () -> (forall x. c x -> l () -> f (l x)) -> (l p -> a) -> Latent sig l f a

deriving instance Functor (Latent sig l f)

instance HFunctor (Latent sig l) where
    hmap k (Node sub l st c) = Node sub l (fmap k . st) c
    {-# INLINE hmap #-}

-- | Type for indicating that a latent operation has no subcomputations
data NoSub :: Type -> Type

-- | Eliminator for 'NoSub'
absurdNoSub :: NoSub a -> b
absurdNoSub x = case x of {}
{-# INLINE absurdNoSub #-}

-- | Type for indicating that a latent operation has exactly one subcomputation
data OneSub v :: Type -> Type where
    One :: OneSub v v

{- | Class for substructural effect inclusion

Provides injection and projection for higher-order signatures
-}
class (sub :: Type -> (Type -> Type) -> Type) :<<: sup where
    -- | Inject an effect into a signature
    inj3 :: sub p c -> sup p c

    -- | Project from a signature to an effect (if possible)
    prj3 :: sup p c -> Maybe (sub p c)

-- | Sum of two higher-order effect signatures
data ((sig1 :: Type -> (Type -> Type) -> Type) :+++: sig2) p c
    = Inl3 (sig1 p c)
    | Inr3 (sig2 p c)

-- | Effect is head of signature
instance {-# OVERLAPPING #-} sig1 :<<: (sig1 :+++: sig2) where
    inj3 = Inl3
    prj3 (Inl3 sig) = Just sig
    prj3 _ = Nothing

-- | Effect is contained within the rest of the signature
instance {-# OVERLAPPABLE #-} (sig :<<: sig2) => sig :<<: (sig1 :+++: sig2) where
    inj3 = Inr3 . inj3
    prj3 (Inr3 sig) = prj3 sig
    prj3 _ = Nothing

-- | Empty higher-order signature
data LVoid p c deriving (Functor)

{- | Complete effect signature combining algebraic, scoped, and latent effects

* 'A': Algebraic effects
* 'S': Scoped effects
* 'L': Latent effects
-}
data Sig sig sigs sigl l f a = A (Algebraic sig f a) | S (Scoped sigs f a) | L (Latent sigl l f a)
    deriving (Functor)

-- | Inject an algebraic effect into the effect signature
injectA
    :: (eff :<: sig, TermMonad m (Sig sig sigs sigl l), Functor eff)
    => eff (m a)
    -> m a
injectA e = con (A (Algebraic (inj e)))
{-# INLINE injectA #-}

-- | Inject a scoped effect into the effect signature
injectS :: forall sig sigs sigl l m a eff. (eff :<: sigs, TermMonad m (Sig sig sigs sigl l), Functor eff) => eff (m (m a)) -> m a
injectS = con . S . Enter . inj
{-# INLINE injectS #-}

-- | Inject a latent effect into the effect signature
injectL
    :: (eff :<<: sigl, TermMonad m (Sig sig sigs sigl l))
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

-- | Constraint synonym for effect monads
type EffectMonad m sig sigs sigl l = (TermMonad m (Sig sig sigs sigl l), Functor l)
