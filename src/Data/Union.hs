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

{- |
Type-level union for effect signatures

This module provides a union type that can hold values from
different functors. It is used as the foundation
for extensible signature types.
-}
module Data.Union (Union (..), Elem, inj, prj, (#), absurd) where

import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

{- | Type synonym for effect lists
Represents a list of effect functors that can be combined in a Union.
-}
type Effects = [Type -> Type]

{- | Union consisting of a list of effect functors and an 'Index'

The Union type can hold a value from any functor in the effect list @effs@
applied to @a@.
The 'Index' proves that the contained functor is a member of the list at a
given position.
-}
data Union (effs :: Effects) a where
    Union :: (Functor f) => !(Index f effs) -> f a -> Union effs a

deriving instance Functor (Union effs)

-- | Index into an effect list, which proves membership of an effect in a list
newtype Index (e :: k) (effs :: [k]) = Index Int
    deriving (Show)

{- | Processing operator for Union types

* Takes a function that processes the head element
* Takes a function that processes the rest list
* Processes the Union by pattern matching on the 'Index'

Used to process a Union by applying the appropriate function based on
which functor is actually present.
-}
(#) :: (f a -> b) -> (Union effs a -> b) -> Union (f : effs) a -> b
(#) alg fwd (Union !p x) = case p of
    Index 0 -> alg (unsafeCoerce x)
    Index n -> fwd (Union (Index (n - 1)) x)
{-# INLINE (#) #-}

-- | Processor for empty union
absurd :: Union '[] a -> a
absurd _ = error "empty union"
{-# INLINE absurd #-}

{- | Type class for proving membership in an effect list

Instances of this class provide an 'Index' proving that effect @f@
is a member of the effect list @effs@.
-}
class Elem (f :: (Type -> Type)) (effs :: Effects) where
    {- | Get the index of effect @f@ in the effect list @effs@.
    Returns an Index that can be used to inject into or project from a Union.
    -}
    elemAt :: Index f effs

-- | effect @e@ is the first element in the list
instance {-# OVERLAPPING #-} Elem e (e ': effs) where
    elemAt = Index 0
    {-# INLINE elemAt #-}

-- | effect @e@ appears later in the list
instance (Elem e effs) => Elem e (_e ': effs) where
    elemAt = case elemAt @e @effs of Index n -> Index $ n + 1
    {-# INLINE elemAt #-}

{- | Inject a value into a union at the appropriate index

* Uses the 'Elem' instance to get the correct 'Index'
* Wraps the value in a Union with the appropriate 'Index'

This is the primary way to create union values from effect values.
-}
inj :: forall f r a. (Functor f, Elem f r) => f a -> Union r a
inj = Union elemAt
{-# INLINE inj #-}

{- | Project a value from a union if it matches the expected effect type

* Uses the 'Elem' instance to get the correct 'Index'
* The projection can fail if the value at hand does not have the expected type
* Uses 'unsafeCoerce' to convert between types when the index matches

This is the primary way to extract effect values from Union values.
-}
prj :: forall f r a. (Elem f r) => Union r a -> Maybe (f a)
prj (Union (Index n) x) = case elemAt @f @r of
    Index m
        | n == m -> Just (unsafeCoerce x)
        | otherwise -> Nothing
{-# INLINE prj #-}

-- >>> elemAt :: Index Maybe '[Maybe, []]
-- Index 0
