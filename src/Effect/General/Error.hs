{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveTraversable #-}

module Effect.General.Error (
    Err (..),
    Error (..),
    runError,
    runErrorC,
    runErrorSmart,
    ErrorL,
    EC,
) where

import Free
import Signature

newtype Err a = Err String
    deriving (Functor, Show)

data Error a = Error String | EOther a
    deriving (Functor, Show, Traversable, Foldable)

instance Applicative Error where
    pure = EOther
    {-# INLINE pure #-}
    Error s <*> _ = Error s
    _ <*> Error s = Error s
    EOther f <*> EOther x = EOther (f x)

instance Monad Error where
    Error s >>= _ = Error s
    EOther x >>= f = f x

instance Pointed Error where
    point = EOther
    {-# INLINE point #-}

runError
    :: (EffectMonad m sig sigs sigl (ErrorL l))
    => Prog (Sig (Err :+: sig) sigs sigl l) a
    -> m (Error a)
runError = unEC . fold point con
{-# INLINE runError #-}

runErrorSmart
    :: (EffectMonad m sig sigs sigl (ErrorL l))
    => SmartProg (Sig (Err :+: sig) sigs sigl l) a
    -> m (Error a)
runErrorSmart = unEC . smartFold point con
{-# INLINE runErrorSmart #-}

instance OuterCarrier EC Error
instance DeriveForward 'Outer EC ErrorL
instance LCarrier ErrorL Error where
    concatM (Error s) = pure (Error s)
    concatM (EOther x) = x
    {-# INLINE concatM #-}

    concatML (Error s) = pure (ErrorL $ Error s)
    concatML (EOther x) = x
    {-# INLINE concatML #-}

algE :: (Pointed m) => Err (m (Error a)) -> m (Error a)
algE (Err s) = point (Error s)

instance (EffectMonad m sig sigs sigl (ErrorL l)) => TermAlgebra (EC m) (Sig (Err :+: sig) sigs sigl l) where
    con (A (Algebraic op)) = (wrap algE # (afwd . Algebraic)) op
    con (S op) = sfwd op
    con (L op) = lfwd op
    {-# INLINE con #-}
    var = EC . gen'Error
      where
        gen'Error x = return (EOther x)
    {-# INLINE var #-}

runErrorC :: (EffectMonad m sig sigs sigl (ErrorL l)) => Cod (EC m) a -> m (Error a)
runErrorC = unEC . runCod var
{-# INLINE runErrorC #-}

newtype EC m a = EC {unEC :: m (Error a)}

instance (Functor m) => Functor (EC m) where
    fmap f (EC x) = EC (fmap (fmap f) x)
    {-# INLINE fmap #-}

instance (Pointed m) => Pointed (EC m) where
    point x = EC $ point (EOther x)
    {-# INLINE point #-}

newtype ErrorL l a = ErrorL {unErrorL :: Error (l a)}
    deriving (Show)

instance (Functor l) => Functor (ErrorL l) where
    fmap f (ErrorL x) = ErrorL (fmap (fmap f) x)
    {-# INLINE fmap #-}