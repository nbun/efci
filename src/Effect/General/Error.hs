{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.General.Error where

import Free
import Signature

newtype Err a = Err String

instance Functor Err where
  fmap _ (Err s) = Err s
  {-# INLINE fmap #-}

data Error a = Error String | EOther a
  deriving (Show)

instance Functor Error where
  fmap _ (Error s) = Error s
  fmap f (EOther x) = EOther (f x)
  {-# INLINE fmap #-}

runError
  :: forall sig sigs sigl l a
   . (Functor sig, Functor sigs)
  => Prog (Sig (Err :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl (ErrorL l)) (Error a)
runError = unEC . fold point con
{-# INLINE runError #-}

instance (EffectMonad m sig sigs sigl (ErrorL l)) => TermAlgebra (EC m) (Sig (Err :+: sig) sigs sigl l) where
  con (A (Algebraic op)) = EC . (algE # afwd) . fmap unEC $ op
   where
    algE (Err s) = return (Error s)
    afwd = con . A . Algebraic
  con (S (Enter op)) = EC $ con $ S $ Enter $ fmap (fmap lift . unEC . fmap unEC) op
  con (L (Node op l st k)) = EC $ con $ L $ Node op (ErrorL (EOther l)) (st' st) k'
   where
    st' st2 c l' = lift2 (fmap (\x -> ErrorL <$> unEC (st2 c x)) (unErrorL l'))
    k' = lift . fmap (unEC . k) . unErrorL
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

instance (Monad m) => Pointed (EC m) where
  point x = EC $ return (EOther x)
  {-# INLINE point #-}

instance Lift ErrorL Error where
  lift (Error s) = return (Error s)
  lift (EOther x) = x
  {-# INLINE lift #-}

  lift2 (Error s) = return (ErrorL $ Error s)
  lift2 (EOther x) = x
  {-# INLINE lift2 #-}

newtype ErrorL l a = ErrorL {unErrorL :: Error (l a)}
  deriving (Show)

instance (Functor l) => Functor (ErrorL l) where
  fmap f (ErrorL x) = ErrorL (fmap (fmap f) x)
  {-# INLINE fmap #-}