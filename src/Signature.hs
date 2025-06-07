{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}

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
    Lift (..),
    OneSub (..),
    LVoid,
    (:<<<:),
    injV,
    Union,
    absurd,
    (:.:),
    prj3,
    HasCallStack
    
) where

import Data.Kind (Type)
import Data.Union
import Free
import GHC.Base (Constraint)
import GHC.Stack (HasCallStack)
import Data.Coerce
import Unsafe.Coerce (unsafeCoerce)

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

instance Applicative Id where
    Id f <*> Id x = Id (f x)
    pure = Id

newtype Algebraic sig (f :: Type -> Type) a = Algebraic (Union sig a) deriving (Functor)

instance HFunctor (Algebraic sig) where
    hmap _ (Algebraic op) = Algebraic op

newtype Scoped sig f a where
    Enter :: Union sig (f a) -> Scoped sig f a
    deriving (Functor)

instance HFunctor (Scoped sig) where
    hmap k (Enter sc) = Enter (fmap k sc)

data Latent sig l f a where
    Node :: sig p c -> l () -> (forall x. c x -> l () -> f (l x)) -> (l p -> a) -> Latent sig l f a

instance Functor (Latent sig l f) where
    fmap f (Node sub l st c) = Node sub l st (f . c)

instance HFunctor (Latent sig l) where
    hmap k (Node sub l st c) = Node sub l (fmap k . st) c

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

instance Functor f => Functor (Sig sig sigs sigl l f) where
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

class Lift g h | g -> h, h -> g where
    lift
        :: (TermMonad m (Sig sig sigs sigl (g l)))
        => h (m (h a))
        -> m (h a)

    lift2
        :: (TermMonad m (Sig sig sigs sigl (g l)))
        => h (m (g l x))
        -> m (g l x)

type EffectMonad m sig sigs sigl l = (TermMonad m (Sig sig sigs sigl l))

-- {-# RULES "fmapCoerce/coerce" fmap coerce = unsafeCoerce #-}