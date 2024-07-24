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

module Signature where

import Data.Kind (Type)
import Free
import GHC.Base (Constraint)

data (sig1 :+: sig2) a
  = Inl (sig1 a)
  | Inr (sig2 a)
  deriving (Functor)

infixr 0 :+:

(#) :: (k1 a -> b) -> (k2 a -> b) -> (k1 :+: k2) a -> b
(f # _) (Inl l) = f l
(_ # g) (Inr r) = g r

data Void a deriving (Functor)

data ((sig1 :: Type -> (Type -> Type) -> Type) :+++: sig2) p c
  = Inl3 (sig1 p c)
  | Inr3 (sig2 p c)

data HVoid (f :: Type -> Type) a deriving (Functor)

runHVoid :: Prog HVoid a -> a
runHVoid (Return x) = x
runHVoid (Call op) = case op of {}

instance HFunctor HVoid where
  hmap f x = case x of {}

class (Functor sub, Functor sup) => (sub :: (Type -> Type)) :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance (Functor sig1) => sig1 :<: sig1 where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-} (Functor sig1, Functor sig2) => sig1 :<: (sig1 :+: sig2) where
  inj = Inl
  prj (Inl sig) = Just sig
  prj _ = Nothing

instance {-# OVERLAPPABLE #-} (Functor sig, Functor sig1, sig :<: sig2) => sig :<: (sig1 :+: sig2) where
  inj = Inr . inj
  prj (Inr sig) = prj sig
  prj _ = Nothing

type family (:.:) effs sig :: Constraint where
  '[] :.: sig = ()
  (x ': xs) :.: sig = (x :<: sig, xs :.: sig)

class (sub :: (Type -> Type) -> Type -> Type) :<<: sup where
  inj2 :: sub f a -> sup f a
  prj2 :: sup f a -> Maybe (sub f a)

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

newtype Algebraic sig (f :: Type -> Type) a = Algebraic (sig a) deriving (Functor, Show)

instance (Functor sig) => HFunctor (Algebraic sig) where
  hmap _ (Algebraic op) = Algebraic op

newtype Scoped sig f a where
  Enter :: sig (f a) -> Scoped sig f a
  deriving (Functor, Show)

instance (Functor sig) => HFunctor (Scoped sig) where
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

data Sig sig sigs sigl l f a = A (Algebraic sig f a) | S (Scoped sigs f a) | L (Latent sigl l f a) deriving (Functor)

injectS
  :: (eff :<: sigs)
  => eff (Prog (Sig sig sigs sigl l) (Prog (Sig sig sigs sigl l) a))
  -> Prog (Sig sig sigs sigl l) a
injectS = Call . S . Enter . inj

injectA
  :: (eff :<: sig)
  => eff (Prog (Sig sig sigs sigl l) a)
  -> Prog (Sig sig sigs sigl l) a
injectA = Call . A . Algebraic . inj

injectL
  :: (eff :<<<<: sigl)
  => eff p c
  -> l ()
  -> ( forall x
        . c x
       -> l ()
       -> Prog (Sig sig sigs sigl l) (l x)
     )
  -> ( l p
       -> Prog (Sig sig sigs sigl l) a
     )
  -> Prog (Sig sig sigs sigl l) a
injectL op l st k = Call $ L $ Node (inj3 op) l st k

instance (Functor sig, Functor sigs) => HFunctor (Sig sig sigs sigl l) where
  hmap f (A a) = A (hmap f a)
  hmap f (S s) = S (hmap f s)
  hmap f (L l) = L (hmap f l)

class Forward f where
  afwd :: (Functor sig, Functor sigs) => sig (f sig sigs sigl l a) -> f sig sigs sigl l a

  sfwd
    :: (Functor sig, Functor sigs)
    => sigs (f sig sigs sigl l (f sig sigs sigl l a))
    -> f sig sigs sigl l a

  lfwd
    :: (Functor sig, Functor sigs)
    => sigl p c
    -> l ()
    -> (forall x. c x -> l () -> f sig sigs sigl l (l x))
    -> (l p -> f sig sigs sigl l a)
    -> f sig sigs sigl l a

class Lift g h | g -> h, h -> g where
  lift
    :: (Functor sig, Functor sigs)
    => h (Prog (Sig sig sigs sigl (g l)) (h a))
    -> Prog (Sig sig sigs sigl (g l)) (h a)

  lift2
    :: (Functor sig, Functor sigs)
    => h (Prog (Sig sig sigs sigl (g l)) (g l x))
    -> Prog (Sig sig sigs sigl (g l)) (g l x)

aalg
  :: (Forward f, Functor sig, Functor sigs)
  => (eff (f sig sigs sigl l a) -> f sig sigs sigl l a)
  -> Sig (eff :+: sig) sigs sigl l (f sig sigs sigl l) (f sig sigs sigl l a)
  -> f sig sigs sigl l a
aalg alg (A (Algebraic op)) = (alg # afwd) op
aalg _ (S (Enter op)) = sfwd op
aalg _ (L (Node op l st k)) = lfwd op l st k

salg
  :: (Forward f, Functor sig, Functor sigs)
  => (eff (f sig sigs sigl l (f sig sigs sigl l a)) -> f sig sigs sigl l a)
  -> Sig sig (eff :+: sigs) sigl l (f sig sigs sigl l) (f sig sigs sigl l a)
  -> f sig sigs sigl l a
salg _ (A (Algebraic op)) = afwd op
salg alg (S (Enter op)) = (alg # sfwd) op
salg _ (L (Node op l st k)) = lfwd op l st k

asalg
  :: (Forward f, Functor sig, Functor sigs)
  => (aeff (f sig sigs sigl l a) -> f sig sigs sigl l a)
  -> (seff (f sig sigs sigl l (f sig sigs sigl l a)) -> f sig sigs sigl l a)
  -> Sig (aeff :+: sig) (seff :+: sigs) sigl l (f sig sigs sigl l) (f sig sigs sigl l a)
  -> f sig sigs sigl l a
asalg alga _ (A (Algebraic op)) = (alga # afwd) op
asalg _ algs (S (Enter op)) = (algs # sfwd) op
asalg _ _ (L (Node op l st k)) = lfwd op l st k

lalg
  :: forall f sig sigs sigl eff l a
   . (Forward f, Functor sig, Functor sigs)
  => ( forall p c
        . eff p c
       -> l ()
       -> (forall x. c x -> l () -> f sig sigs sigl l (l x))
       -> (l p -> f sig sigs sigl l a)
       -> f sig sigs sigl l a
     )
  -> Sig sig sigs (eff :+++: sigl) l (f sig sigs sigl l) (f sig sigs sigl l a)
  -> f sig sigs sigl l a
lalg _ (A (Algebraic op)) = afwd op
lalg _ (S (Enter op)) = sfwd op
lalg alg (L (Node (Inl3 op) l st k)) = alg op l st k
lalg _ (L (Node (Inr3 op) l st k)) = lfwd op l st k