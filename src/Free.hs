{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Effect representations

This module provides the foundational effect implementations used throughout
the interpreter. It includes:

* Free monad ('Prog') for building effectful programs
* Higher-order functors ('HFunctor') for effect interpretation
* Smart representation ('SmartProg') with optimized view-based interpretation
* 'Codensity' representation with fusion performance optimization
* 'TermAalgebra' classe for generic effect creation/handling
-}
module Free (
    Prog (..),
    HFunctor (..),
    Pointed (..),
    TermMonad,
    SmartProg (..),
    Cod (..),
    TermAlgebra (..),
    fold,
    smartFold,
    runCod,
    finish,
) where

{- | Free monad for effectful programs

* 'Return': Pure value
* 'Call': Effectful operation with functor @k@
-}
data Prog k a where
    Return :: a -> Prog k a
    Call :: k (Prog k) (Prog k a) -> Prog k a

instance (forall f. (Functor f) => Functor (k f)) => Functor (Prog k) where
    fmap f (Return x) = Return (f x)
    fmap f (Call op) = Call (fmap (fmap f) op)

{- | Type synonym for natural transformations

Represents a natural transformation between two functors @f@ and @g@.
-}
type f --> g = forall a. f a -> g a

{- | Higher-order functor class

Functors that can be mapped over other functors. This is essential
for the effect implementation as it allows flexibility w.r.t. sub-
computations and how they are treated.
-}
class (forall f. (Functor f) => Functor (k f)) => HFunctor k where
    -- | Higher-order map: apply a natural transformation to the functor
    hmap :: (Functor f, Functor f') => f --> f' -> k f --> k f'

instance (forall f. (Functor f) => Functor (k f)) => Applicative (Prog k) where
    pure = Return
    Return f <*> p = fmap f p
    Call op <*> p = Call (fmap (<*> p) op)
    {-# INLINE (<*>) #-}

instance (forall f. (Functor f) => Functor (k f)) => Monad (Prog k) where
    Return x >>= f = f x
    Call op >>= f = Call (fmap (>>= f) op)
    {-# INLINE (>>=) #-}

{- | Fold for free monads

Folds a free monad computation into a target type @f@ using:
* @gen@: generator for extending pure values
* @alg@: algebra for effect operations
-}
fold :: forall k f a b. (HFunctor k, Pointed f) => (a -> f b) -> (forall x. k f (f x) -> f x) -> Prog k a -> f b
fold gen alg = go
  where
    go :: Prog k a -> f b
    go (Return x) = gen x
    go (Call op) = alg (hmap fold' (fmap go op))

    fold' :: Prog k --> f
    fold' (Return x) = point x
    fold' (Call op) = alg (hmap fold' (fmap fold' op))

{- | Optimized fold for 'SmartProg'

Similar to 'fold' but uses the view-based 'SmartProg' type for better
performance. Uses pattern matching on the view to avoid unnecessary
traversal of intermediate representations.
-}
smartFold :: forall k f a b. (HFunctor k, Pointed f) => (a -> f b) -> (forall x. k f (f x) -> f x) -> SmartProg k a -> f b
smartFold gen alg = go
  where
    go :: SmartProg k a -> f b
    go p = case view p of
        ViewReturn x -> gen x
        ViewCall op -> alg (hmap fold' (fmap go op))

    fold' :: SmartProg k --> f
    fold' p = case view p of
        ViewReturn x -> point x
        ViewCall op -> alg (hmap fold' (fmap fold' op))

-- | Class for pointed functors (functors with a pure/pure-like operation)
class (Functor f) => Pointed f where
    point :: a -> f a
    default point :: (Applicative f) => a -> f a
    point = pure

instance Pointed []
instance Pointed ((->) r)
instance Pointed IO
instance (HFunctor k) => Pointed (Prog k) where
    point = Return
    {-# INLINE point #-}

{- | Term algebra class

Provides an abstract interface for effect representations.
-}
class (HFunctor k) => TermAlgebra h k | h -> k where
    -- | Lift a value into the effect representation @h@
    var :: a -> h a

    -- | Wrap an operation of type @k@ using the effect representation @h@
    con :: k h (h a) -> h a

    -- | Inspect the root operation of an effect representation (if possible)
    peek :: h a -> Maybe (k h (h a))
    peek _ = Nothing

instance (HFunctor sig) => TermAlgebra (Prog sig) sig where
    var = Return
    {-# INLINE var #-}
    con = Call
    {-# INLINE con #-}
    peek (Call op) = Just op
    peek _ = Nothing
    {-# INLINE peek #-}

{- | Class for term algebras with monadic structure

Combines 'Monad', 'TermAlgebra', and 'Pointed' constraints for convenient usage.
-}
class (Monad m, TermAlgebra m f, Pointed m) => TermMonad m f | m -> f

instance (Monad m, TermAlgebra m f, Pointed m) => TermMonad m f

{- | Codensity monad

The codensity monad provides better performance characteristics
for free monad interpretation by using continuation-passing style.
-}
newtype Cod h a = Cod {unCod :: forall x. (a -> h x) -> h x}
    deriving (Functor)

instance Pointed (Cod h)

instance Applicative (Cod h) where
    pure x = Cod ($ x)
    {-# INLINE pure #-}
    Cod m <*> Cod n = Cod (\k -> m (\f -> n (k . f)))
    {-# INLINE (<*>) #-}

instance Monad (Cod h) where
    Cod m >>= f = Cod (\k -> m (\a -> unCod (f a) k))
    {-# INLINE (>>=) #-}

instance (Pointed h, TermAlgebra h f) => TermAlgebra (Cod h) f where
    var = return
    {-# INLINE var #-}
    con = algCod con
    {-# INLINE con #-}
    peek _ = Nothing
    {-# INLINE peek #-}

-- | Convert an algebra to work with 'Cod'
algCod :: forall f h a. (HFunctor f, Pointed h) => (forall x. f h (h x) -> h x) -> (f (Cod h) (Cod h a) -> Cod h a)
algCod alg !op = Cod (\k -> alg (fmap (\(Cod m) -> m k) (hmap (\(Cod m) -> m point) op)))
{-# INLINE algCod #-}

-- | Run a 'Cod' computation with a given continuation
runCod :: (a -> f x) -> Cod f a -> f x
runCod g m = unCod m g
{-# INLINE runCod #-}

-- | Extract the result from a 'Cod' value using the term algebra's 'var' operation
finish :: (TermAlgebra h f) => Cod h x -> h x
finish m = unCod m var
{-# INLINE finish #-}

{- | Effect representation based on smart views

This variant of the free monad uses a view-based approach:

* 'SmartReturn': Pure value
* 'SmartCall': Effectful operation
* 'SmartBind': Bind operation
-}
data SmartProg k a where
    SmartReturn :: a -> SmartProg k a
    SmartCall :: k (SmartProg k) (SmartProg k a) -> SmartProg k a
    SmartBind :: SmartProg k a -> (a -> SmartProg k b) -> SmartProg k b

deriving instance (Functor (k (SmartProg k))) => Functor (SmartProg k)

instance (HFunctor k) => Applicative (SmartProg k) where
    pure = SmartReturn
    {-# INLINE pure #-}
    SmartReturn f <*> p = fmap f p
    SmartCall op <*> p = SmartCall (fmap (<*> p) op)
    SmartBind p g <*> q = SmartBind p (\x -> g x <*> q)
    {-# INLINE (<*>) #-}

instance (HFunctor k) => Monad (SmartProg k) where
    x >>= f = SmartBind x f
    {-# INLINE (>>=) #-}

{- | View type for 'SmartProg'

Used for optimized pattern matching on 'SmartProg' values.
This avoids some of the overhead of the standard free monad approach.
-}
data ProgView k a where
    ViewReturn :: a -> ProgView k a
    ViewCall :: k (SmartProg k) (SmartProg k a) -> ProgView k a

{- | View-based pattern matching for 'SmartProg'

Returns a view that allows efficient pattern matching on the 'SmartProg' structure.
-}
view :: (HFunctor k) => SmartProg k a -> ProgView k a
view (SmartReturn x) = ViewReturn x
view (SmartCall op) = ViewCall op
view (SmartBind (SmartBind m f) g) = view (SmartBind m (\x -> SmartBind (f x) g))
view (SmartBind (SmartReturn x) f) = view (f x)
view (SmartBind (SmartCall op) f) = ViewCall (fmap (`SmartBind` f) op)
{-# INLINE view #-}

instance (HFunctor sig) => TermAlgebra (SmartProg sig) sig where
    var = SmartReturn
    {-# INLINE var #-}
    con = SmartCall
    {-# INLINE con #-}
    peek p = case view p of
        ViewCall op -> Just op
        _ -> Nothing
    {-# INLINE peek #-}

instance (HFunctor k) => Pointed (SmartProg k)