{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
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
  :: forall tag r sig sigs sigl
   . (Functor sig, Functor sigs)
  => (ReaderF tag r :<: sig)
  => Prog (Sig sig sigs sigl Id) r
ask = ctrace "ask" $ Call (A (Algebraic (inj (Ask @tag return))))

runReader
  :: (Functor sig, Functor sigs)
  => r
  -> Prog (Sig (ReaderF tag r :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl l) a
runReader r p = hReader p r

hReader
  :: (Functor sig, Functor sigs)
  => Prog (Sig (ReaderF tag r :+: sig) sigs sigl l) a
  -> (r -> Prog (Sig sig sigs sigl l) a)
hReader = ctrace "runReader" . unR . fold point (aalg algR)
 where
  algR :: ReaderF tag r (R r sig sigs sigl l x) -> R r sig sigs sigl l x
  algR (Ask k) = R (\r -> unR (k r) r)

instance Forward (R r) where
  afwd op = R (\r -> Call (A (Algebraic (fmap (\k -> unR k r) op))))
  sfwd op = R $ \r -> Call $ S $ Enter $ fmap (go r) op
   where
    go r hhx = do
      hx <- unR hhx r
      return (unR hx r)
  lfwd op l st k = R $ \r -> Call $ L $ Node op l (st' r) (k' r)
   where
    st' r c lv = unR (st c lv) r
    k' r lv = unR (k lv) r

newtype R r sig sigs sigl l a = R {unR :: r -> Prog (Sig sig sigs sigl l) a}
  deriving (Functor)

instance (Functor sig, Functor sigs) => Pointed (R r sig sigs sigl l) where
  point x = R $ \_ -> return x

data FunctionReader

type Declarations sig sigs sigl a =
  ReaderF FunctionReader [AEProg (Prog (Sig sig sigs sigl Id) a)]