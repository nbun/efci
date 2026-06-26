{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Union (Union (..), Elem, inj, prj, (#), absurd) where

import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

type Effects = [Type -> Type]

data Union (effs :: Effects) a where
    Union :: (Functor f) => !(Index f effs) -> f a -> Union effs a
deriving instance Functor (Union effs)

newtype Index (e :: k) (effs :: [k]) = Index Int
    deriving (Show)

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

instance (Elem e effs) => Elem e (_e ': effs) where
    elemAt = case elemAt @e @effs of Index n -> Index $ n + 1
    {-# INLINE elemAt #-}

inj :: forall f r a. (Functor f, Elem f r) => f a -> Union r a
inj = Union elemAt
{-# INLINE inj #-}

prj :: forall f r a. (Elem f r) => Union r a -> Maybe (f a)
prj (Union (Index n) x) = case elemAt @f @r of
    Index m
        | n == m -> Just (unsafeCoerce x)
        | otherwise -> Nothing
{-# INLINE prj #-}

-- >>> elemAt :: Index Maybe '[Maybe, []]
-- Index 0
