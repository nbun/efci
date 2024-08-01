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

module Effect.General.Reader where

import Debug (ctrace)
import Free
import Signature
import Type (AEProg)

newtype ReaderF tag r a = Ask (r -> a)
  deriving (Functor)

ask
  :: forall tag r sig sigs sigl l m
   . (ReaderF tag r :<: sig, TermMonad m (Sig sig sigs sigl l))
  => m r
ask = ctrace "ask" $ injectA (Ask @tag return)
{-# INLINE ask #-}

runReader :: forall tag sig sigs sigl l r a. 
   (Functor sig, Functor sigs)
  => r
  -> Prog (Sig (ReaderF tag r :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl l) a
runReader r p = hReader p r

runReaderC :: forall tag m sig sigs sigl l r a. (EffectMonad m sig sigs sigl l) => r -> Cod (RC tag r m) a -> m a
runReaderC r p = unRC (runCod var p) r
{-# INLINE runReaderC #-}

hReader
  :: (Functor sig, Functor sigs)
  => Prog (Sig (ReaderF tag r :+: sig) sigs sigl l) a
  -> (r -> Prog (Sig sig sigs sigl l) a)
hReader = ctrace "runReader" . unRC . fold point con

instance (EffectMonad m sig sigs sigl l) => TermAlgebra (RC tag r m) (Sig (ReaderF tag r :+: sig) sigs sigl l) where
  con (A (Algebraic op)) = RC . (algR # afwd) . fmap unRC $ op
   where
    algR (Ask k) r = k r r
    afwd op r = con (A (Algebraic (fmap (\k -> k r) op)))
  con (S (Enter op)) = RC $ \r -> con $ S $ Enter $ fmap (go r) op
   where
    go r hhx = do
      hx <- unRC hhx r
      return (unRC hx r)
  con (L (Node op l st k)) = RC $ \r -> con $ L $ Node op l (st' st r) (k' r)
   where
    st' st r c lv = unRC (st c lv) r
    k' r lv = unRC (k lv) r
  {-# INLINE con #-}
  var = RC . gen'Reader
   where
    gen'Reader x = return . const x
  {-# INLINE var #-}

newtype RC tag r m a = RC {unRC :: r -> m a}

instance (Functor m) => Functor (RC tag r m) where
  fmap f (RC x) = RC (fmap f . x)

instance (Monad m) => Pointed (RC tag r m) where
  point x = RC $ const (return x)
  {-# INLINE point #-}

data FunctionReader

type Declarations m a =
  ReaderF FunctionReader [AEProg (m a)]