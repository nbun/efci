{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Effect.General.ND (
    choose,
    failed,
    ND,
    (?),
    runND,
    runNDC,
    runNDSmart,
    ListL,
    NDC,
) where

import Effect.General.State (EffectCons, logCall)
import Free
import GHC.Conc
import Signature
import Data.Coerce (coerce)

data ND a = Fail | Or a a

instance Functor ND where
    fmap _ Fail = Fail
    fmap f (Or l r) =
        let l' = f l
            r' = f r
         in pseq (par l' r') (Or l' r')
    {-# INLINE fmap #-}

(?)
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => m a
    -> m a
    -> m a
(?) p1 p2 = logCall >> injectA (Or p1 p2)
{-# INLINE (?) #-}

failed
    :: (ND :<: sig, EffectCons m sig sigs sigl l) => m a
failed = logCall >> injectA Fail
{-# INLINE failed #-}

choose
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => [m a]
    -> m a
choose [] = failed
choose (p : ps) = foldr (?) p ps
{-# INLINE choose #-}

runND
    :: forall sig sigs sigl l a
     . Prog (Sig (ND :+: sig) sigs sigl l) a
    -> Prog (Sig sig sigs sigl (ListL l)) [a]
runND = unNDC . fold point con
{-# INLINE runND #-}

runNDSmart
    :: forall sig sigs sigl l a
     . SmartProg (Sig (ND :+: sig) sigs sigl l) a
    -> SmartProg (Sig sig sigs sigl (ListL l)) [a]
runNDSmart = unNDC . smartFold point con
{-# INLINE runNDSmart #-}

runNDC :: (EffectMonad m sig sigs sigl (ListL l)) => Cod (NDC m) a -> m [a]
runNDC = unNDC . runCod var
{-# INLINE runNDC #-}

algND :: (Applicative m) => ND (m [a]) -> m [a]
algND Fail = pure []
algND (Or l r) = (++) <$> l <*> r

instance (EffectMonad m sig sigs sigl (ListL l)) => TermAlgebra (NDC m) (Sig (ND :+: sig) sigs sigl l) where
    con op = case op of
        A (Algebraic op') -> (wrap algND # (afwd . Algebraic)) op'
        S op' -> sfwd op'
        L op' -> lfwd op'
    {-# INLINE con #-}
    var = cc . point . point
    {-# INLINE var #-}

newtype NDC m a = NDC {unNDC :: m [a]}

instance OuterCarrier NDC []
instance DeriveForward 'Outer NDC ListL

instance (Functor m) => Functor (NDC m) where
    fmap f = NDC . fmap (fmap f) . unNDC
    {-# INLINE fmap #-}

instance (Pointed m) => Pointed (NDC m) where
    point = NDC . point . point
    {-# INLINE point #-}

newtype ListL l a = ListL {unListL :: [l a]}
    deriving (Show)

instance (Functor l) => Functor (ListL l) where
    fmap f (ListL la) = ListL (fmap f <$> la)
    {-# INLINE fmap #-}

instance LCarrier ListL [] where
    lift = foldr (liftA2 (++)) (pure [])
    lift2 =
        foldr
            (liftA2 (\xs ys -> cl $ unl xs ++ unl ys))
            (pure (cl []))