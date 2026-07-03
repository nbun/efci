{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Error effect

This module provides an effect for producing (critical) errors.
-}
module Effect.General.Error (
    Err (..),
    Error (..),
    runError,
    runErrorC,
    runErrorSmart,
    ErrorL,
    EC,
) where

import Forwarding
import Free
import Signature

{- | Error effect

Wraps an error message string in the effect
-}
newtype Err a = Err String
    deriving (Functor, Show)

{- | Error result type

* 'Error': Represents an error with its message
* 'EOther': Semantic values of other effects
-}
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

-- | Handle error effect with tree-based representation
runError
    :: (EffectMonad m sig sigs sigl (ErrorL l))
    => Prog (Sig (Err :+: sig) sigs sigl l) a
    -> m (Error a)
runError = unEC . fold point con
{-# INLINE runError #-}

-- | Handle error effect using smart views
runErrorSmart
    :: (EffectMonad m sig sigs sigl (ErrorL l))
    => SmartProg (Sig (Err :+: sig) sigs sigl l) a
    -> m (Error a)
runErrorSmart = unEC . smartFold point con
{-# INLINE runErrorSmart #-}

-- | Handle error effect with 'Codensity' representation
runErrorC :: (EffectMonad m sig sigs sigl (ErrorL l)) => Cod (EC m) a -> m (Error a)
runErrorC = unEC . runCod var
{-# INLINE runErrorC #-}

instance Carrier EC Error
instance Forward 'Default EC ErrorL
instance LCarrier ErrorL Error where
    concatM (Error s) = pure (Error s)
    concatM (EOther x) = x
    {-# INLINE concatM #-}

-- | Algebra for handling error effect
algE :: (Pointed m) => Err (m (Error a)) -> m (Error a)
algE (Err s) = point (Error s)

-- | 'TermAlgebra' instance for handling error effect
instance (EffectMonad m sig sigs sigl (ErrorL l)) => TermAlgebra (EC m) (Sig (Err :+: sig) sigs sigl l) where
    con (A (Algebraic op)) = (wrap algE # (afwd . Algebraic)) op
    con (S op) = sfwd op
    con (L op) = lfwd op
    {-# INLINE con #-}
    var = EC . gen'Error
      where
        gen'Error x = return (EOther x)
    {-# INLINE var #-}

{- | Error carrier newtype

Combines other carrier types with 'Error'.
-}
newtype EC m a = EC {unEC :: m (Error a)}

instance (Functor m) => Functor (EC m) where
    fmap f (EC x) = EC (fmap (fmap f) x)
    {-# INLINE fmap #-}

instance (Pointed m) => Pointed (EC m) where
    point x = EC $ point (EOther x)
    {-# INLINE point #-}

{- | Error latent carrier

Combines an 'Error' with a latent carrier @l@.
-}
newtype ErrorL l a = ErrorL {unErrorL :: Error (l a)}
    deriving (Show)

instance (Functor l) => Functor (ErrorL l) where
    fmap f (ErrorL x) = ErrorL (fmap (fmap f) x)
    {-# INLINE fmap #-}