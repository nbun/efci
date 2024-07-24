{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
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
  deriving (Functor)

data Error a = Error String | EOther a
  deriving (Functor, Show)

runError
  :: forall sig sigs sigl l a
   . (Functor sig, Functor sigs)
  => Prog (Sig (Err :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl (ErrorL l)) (Error a)
runError = unEL . fold point (aalg algE)
 where
  algE :: Err (EL sig sigs sigl l x) -> EL sig sigs sigl l x
  algE (Err s) = EL (return (Error s))

newtype EL sig sigs sigl l a = EL {unEL :: Prog (Sig sig sigs sigl (ErrorL l)) (Error a)}
  deriving (Functor)

instance (Functor sig, Functor sigs) => Pointed (EL sig sigs sigl l) where
  point = EL . return . EOther

instance Forward EL where
  afwd op = EL $ Call $ A $ Algebraic $ fmap unEL op
  sfwd op = EL $ Call $ S $ Enter $ fmap (fmap lift . unEL . fmap unEL) op
  lfwd op l st k = EL $ Call $ L $ Node op (ErrorL (EOther l)) (st' st) k'
   where
    st' st2 c l' = lift2 (fmap (\x -> ErrorL <$> unEL (st2 c x)) (unErrorL l'))
    k' = lift . fmap (unEL . k) . unErrorL

instance Lift ErrorL Error where
  lift (Error s) = return (Error s)
  lift (EOther x) = x

  lift2 (Error s) = return (ErrorL $ Error s)
  lift2 (EOther x) = x

newtype ErrorL l a = ErrorL {unErrorL :: Error (l a)}
  deriving (Show, Functor)