{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

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
) where

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

smartFold :: forall k f a b. (HFunctor k, Pointed f) => (a -> f b) -> (forall x. k f (f x) -> f x) -> SmartProg k a -> f b
smartFold gen alg p = case view p of
    (ViewReturn x) -> gen x
    (ViewCall op) -> alg (hmap fold' (fmap (smartFold gen alg) op))
  where
    fold' :: SmartProg k --> f
    fold' p = case view p of
        (ViewReturn x) -> point x
        (ViewCall op) -> alg (hmap fold' (fmap fold' op))

class (Functor f) => Pointed f where
    point :: a -> f a

instance Pointed [] where
    point = return

instance (HFunctor k) => Pointed (Prog k) where
    point = Return

-- fusion for free --

class (HFunctor f) => TermAlgebra h f | h -> f where
    var :: a -> h a
    con :: f h (h a) -> h a
    peek :: h a -> Maybe (f h (h a))

instance (HFunctor sig) => TermAlgebra (Prog sig) sig where
    var = Return
    {-# INLINE var #-}
    con = Call
    {-# INLINE con #-}
    peek (Call op) = Just op
    peek _ = Nothing
    {-# INLINE peek #-}

class (Monad m, TermAlgebra m f, Pointed m) => TermMonad m f | m -> f

instance (Monad m, TermAlgebra m f, Pointed m) => TermMonad m f

-- codensity --

newtype Cod h a = Cod {unCod :: forall x. (a -> h x) -> h x}

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
    peek (Cod m) = Nothing
    {-# INLINE peek #-}

instance Pointed (Cod h) where
    point = pure
    {-# INLINE point #-}

algCod :: forall f h a. (HFunctor f, Pointed h) => (forall x. f h (h x) -> h x) -> (f (Cod h) (Cod h a) -> Cod h a)
algCod alg !op = Cod (\k -> alg (fmap (\(Cod m) -> m k) (hmap (\(Cod m) -> m point) op)))
{-# INLINE algCod #-}

runCod :: (a -> f x) -> Cod f a -> f x
runCod g m = unCod m g
{-# INLINE runCod #-}

finish :: (TermAlgebra h f) => Cod h x -> h x
finish m = unCod m var
{-# INLINE finish #-}

data SmartProg k a where
    SmartReturn :: a -> SmartProg k a
    SmartCall :: k (SmartProg k) (SmartProg k a) -> SmartProg k a
    SmartBind :: SmartProg k a -> (a -> SmartProg k b) -> SmartProg k b

instance (HFunctor k) => Functor (SmartProg k) where
    fmap f (SmartReturn x) = SmartReturn (f x)
    fmap f (SmartCall op) = SmartCall (fmap (fmap f) op)
    fmap f (SmartBind p g) = SmartBind p (fmap f . g)
    {-# INLINE fmap #-}

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

data ProgView k a where
    ViewReturn :: a -> ProgView k a
    ViewCall :: k (SmartProg k) (SmartProg k a) -> ProgView k a

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

instance (HFunctor k) => Pointed (SmartProg k) where
    point = SmartReturn
    {-# INLINE point #-}