{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Free where

data Prog k a where
  Return :: a -> Prog k a
  Call :: k (Prog k) (Prog k a) -> Prog k a

deriving instance (Show (k (Prog k) (Prog k a)), Show a) => Show (Prog k a)

instance (HFunctor k) => Functor (Prog k) where
  fmap f (Return x) = Return (f x)
  fmap f (Call op) = Call (fmap (fmap f) op)

type f --> g = forall a. f a -> g a

class (forall f. (Functor f) => Functor (k f)) => HFunctor k where
  hmap :: (Functor f, Functor f') => f --> f' -> k f --> k f'

instance (HFunctor k) => Monad (Prog k) where
  Return x >>= f = f x
  Call op >>= f = Call (fmap (>>= f) op)

instance (HFunctor k) => Applicative (Prog k) where
  pure = Return
  Return f <*> p = fmap f p
  Call op <*> p = Call (fmap (<*> p) op)

fold :: forall k f a b. (HFunctor k, Pointed f) => (a -> f b) -> (forall x. k f (f x) -> f x) -> Prog k a -> f b
fold gen alg (Return x) = gen x
fold gen alg (Call op) = alg (hmap fold' (fmap (fold gen alg) op))
 where
  fold' :: Prog k --> f
  fold' (Return x) = point x
  fold' (Call op) = alg (hmap fold' (fmap fold' op))

class (Functor f) => Pointed f where
  point :: a -> f a

instance Pointed [] where
  point = return

instance (HFunctor k) => Pointed (Prog k) where
  point = Return

-- fusion for free --

class HFunctor f => TermAlgebra h f | h -> f where
  var :: a -> h a
  con :: f h (h a) -> h a

instance HFunctor sig => TermAlgebra (Prog sig) sig where
  var = Return
  {-# INLINE var #-}
  con = Call
  {-# INLINE con #-}

class (Monad m, TermAlgebra m f, Pointed m) => TermMonad m f | m -> f

instance (Monad m, TermAlgebra m f, Pointed m) => TermMonad m f

-- codensity --

newtype Cod h a = Cod { unCod :: forall x. (a -> h x) -> h x}

instance Functor (Cod h) where
  fmap f m = Cod (\k -> unCod m (k . f))
  {-# INLINE fmap #-}

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

instance Pointed (Cod h) where
  point = pure
  {-# INLINE point #-}

algCod :: forall f h a. (HFunctor f, Pointed h) => (forall x. f h (h x) -> h x) -> (f (Cod h) (Cod h a) -> Cod h a)
algCod alg op = Cod (\k -> alg (hmap (\(Cod m) -> m point) (fmap (\(Cod m) -> m k) op)))
{-# INLINE algCod #-}

runCod :: (a -> f x) -> Cod f a -> f x
runCod g m = unCod m g
{-# INLINE runCod #-}

finish :: TermAlgebra h f => Cod h x -> h x
finish m = unCod m var
{-# INLINE finish #-}