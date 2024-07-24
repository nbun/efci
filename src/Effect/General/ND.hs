{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Effect.General.ND where

import Control.Monad (liftM2)
import Free
import Signature

data ND a = Fail | Or a a
  deriving (Functor)

(?)
  :: (ND :<: sig)
  => Prog (Sig sig sigs sigl l) a
  -> Prog (Sig sig sigs sigl l) a
  -> Prog (Sig sig sigs sigl l) a
(?) p1 p2 = Call (A (Algebraic (inj (Or p1 p2))))

failed
  :: (ND :<: sig)
  => Prog (Sig sig sigs sigl l) a
failed = Call (A (Algebraic (inj Fail)))

choose
  :: (ND :<: sig)
  => [Prog (Sig sig sigs sigl l) a]
  -> Prog (Sig sig sigs sigl l) a
choose [] = failed
choose (p : ps) = foldr (?) p ps

runND
  :: forall sig sigs sigl l a
   . (Functor sig, Functor sigs)
  => Prog (Sig (ND :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl (ListL l)) [a]
runND = unND . fold point (aalg algND)
 where
  algND :: ND (NDC sig sigs sigl l x) -> NDC sig sigs sigl l x
  algND Fail = NDC $ return []
  algND (Or l r) = NDC $ (++) <$> unND l <*> unND r

newtype NDC sig sigs sigl l a = NDC {unND :: Prog (Sig sig sigs sigl (ListL l)) [a]}
  deriving (Functor)

instance (Functor sig, Functor sigs) => Pointed (NDC sig sigs sigl l) where
  point = NDC . return . return

newtype ListL l a = ListL {unListL :: [l a]}
  deriving (Functor, Show)

instance Forward NDC where
  afwd = NDC . Call . A . Algebraic . fmap unND

  sfwd = NDC . Call . S . Enter . fmap (fmap lift . unND . fmap unND)

  lfwd op l st k = NDC $ Call $ L $ Node op (ListL [l]) (st' st) k'
   where
    st' st2 c l' = lift2 (fmap (\x -> ListL <$> unND (st2 c x)) (unListL l'))
    k' = lift . fmap (unND . k) . unListL

instance Lift ListL [] where
  lift = foldr (liftM2 (++)) (return [])
  lift2 =
    foldr
      (liftM2 (\xs ys -> ListL $ unListL xs ++ unListL ys))
      (return (ListL []))