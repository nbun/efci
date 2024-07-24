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