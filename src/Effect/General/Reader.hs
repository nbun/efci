{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE DataKinds #-}

module Effect.General.Reader () where

import Effect.General.State (EffectCons, logCall)
import Free
import Signature
import Type (AEProg)

newtype ReaderF tag r a = Ask (r -> a)
    deriving (Functor)

ask
    :: forall tag r sig sigs sigl l m
     . (ReaderF tag r :<: sig, EffectCons m sig sigs sigl l)
    => m r
ask = logCall >> injectA (Ask @tag return)
{-# INLINE ask #-}

runReader
    :: forall tag sig sigs sigl l r a
     . r
    -> Prog (Sig (ReaderF tag r :+: sig) sigs sigl l) a
    -> Prog (Sig sig sigs sigl l) a
runReader r p = hReader p r

runReaderC :: forall tag m sig sigs sigl l r a. (EffectMonad m sig sigs sigl l) => r -> Cod (RC tag r m) a -> m a
runReaderC r p = unRC (runCod var p) r
{-# INLINE runReaderC #-}

hReader
    :: Prog (Sig (ReaderF tag r :+: sig) sigs sigl l) a
    -> (r -> Prog (Sig sig sigs sigl l) a)
hReader = unRC . fold point con

instance ReaderCarrier (RC tag r) r
instance DeriveForward 'Reader (RC tag r) VoidL

algR :: ReaderF tag r (r -> m a) -> r -> m a
algR (Ask k) r = k r r

instance (EffectMonad m sig sigs sigl l) => TermAlgebra (RC tag r m) (Sig (ReaderF tag r :+: sig) sigs sigl l) where
    con (A (Algebraic op)) = (wrapr algR # (afwd @VoidL . Algebraic)) op 
    con (S op) = sfwd @VoidL op
    con (L op) = lfwd @VoidL op
    {-# INLINE con #-}
    var = RC . \x -> point . const x
    {-# INLINE var #-}

newtype RC tag r m a = RC {unRC :: r -> m a}

instance (Functor m) => Functor (RC tag r m) where
    fmap f (RC x) = RC (fmap f . x)

instance (Pointed m) => Pointed (RC tag r m) where
    point x = RC $ const (point x)
    {-# INLINE point #-}