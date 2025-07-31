{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}

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
    deriving (Functor, Show)

instance Pointed Error where
    point = EOther
    {-# INLINE point #-}

runError
    :: forall sig sigs sigl l a
     . Prog (Sig (Err :+: sig) sigs sigl l) a
    -> Prog (Sig sig sigs sigl (ErrorL l)) (Error a)
runError = unEC . fold point con
{-# INLINE runError #-}

runErrorSmart
    :: forall sig sigs sigl l a
     . SmartProg (Sig (Err :+: sig) sigs sigl l) a
    -> SmartProg (Sig sig sigs sigl (ErrorL l)) (Error a)
runErrorSmart = unEC . smartFold point con
{-# INLINE runErrorSmart #-}

instance OuterCarrier EC Error
instance DeriveForward 'Outer EC ErrorL

algE :: Pointed m => Err (m (Error a)) -> m (Error a)
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


instance LCarrier ErrorL Error where
    lift (Error s) = pure (Error s)
    lift (EOther x) = x
    {-# INLINE lift #-}

    lift2 (Error s) = pure (ErrorL $ Error s)
    lift2 (EOther x) = x
    {-# INLINE lift2 #-}

newtype ErrorL l a = ErrorL {unErrorL :: Error (l a)}
    deriving (Show)

instance (Functor l) => Functor (ErrorL l) where
    fmap f (ErrorL x) = ErrorL (fmap (fmap f) x)
    {-# INLINE fmap #-}