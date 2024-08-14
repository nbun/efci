{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

module Data.Union (Union (..), Elem, inj, (#), absurd) where
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)

type Effects = [Type -> Type]

data Union (effs :: Effects) a where
  Union :: Functor f => Index f effs -> f a -> Union effs a

newtype Index (e :: k) (effs :: [k]) = Index Int

instance Functor (Union r) where
  fmap f (Union p x) = Union p $ f <$> x
  {-# INLINE fmap #-}

(#) :: (f a -> b) -> (Union effs a -> b) -> Union (f : effs) a -> b
(#) alg fwd (Union !p x) = case p of
  Index 0 -> alg (unsafeCoerce x)
  Index n -> fwd (Union (Index (n - 1)) x)
{-# INLINE (#) #-}

absurd :: Union '[] a -> a
absurd _ = error "empty union"
{-# INLINE absurd #-}

class Elem (f :: (Type -> Type)) (effs :: Effects) where
  elemAt :: Index f effs

instance {-# OVERLAPPING #-} Elem e (e ': effs) where
  elemAt = Index 0
  {-# INLINE elemAt #-}

instance Elem e effs => Elem e (_e ': effs) where
  elemAt = case elemAt @e @effs of Index n -> Index $ n + 1
  {-# INLINE elemAt #-}

inj :: forall f r a. (Functor f, Elem f r) => f a -> Union r a
inj = Union elemAt
{-# INLINE inj #-}
