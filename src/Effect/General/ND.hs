{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Non-determinism effect

This module provides an effect for non-deterministic computations.
-}
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

import Effect.General.State (EffectCons, logPrimCall)
import Forwarding
import Free
import GHC.Conc
import Signature

{- | Non-determinism effect operations

* 'Fail': Represents failure/backtracking
* 'Or': Represents choice between two computations
-}
data ND a = Fail | Or a a

instance Functor ND where
    fmap _ Fail = Fail
    -- order-preserving, parallel evaluation of branches
    fmap f (Or l r) =
        let l' = f l
            r' = f r
        in  r' `par` l' `pseq` Or l' r'
    {-# INLINE fmap #-}

{- | Choice operator for non-deterministic computation

Creates a choice between two computations.
-}
(?)
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => m a
    -> m a
    -> m a
(?) p1 p2 = logPrimCall >> injectA (Or p1 p2)
{-# INLINE (?) #-}

{- | Fail operation

Represents a failed branch. If other, non-fail branches exist,
failures are absorbed.
-}
failed
    :: (ND :<: sig, EffectCons m sig sigs sigl l) => m a
failed = logPrimCall >> injectA Fail
{-# INLINE failed #-}

{- | Choose from a list of non-deterministic alternatives

Folds a list of computations with the choice operator from right to left.
-}
choose
    :: (ND :<: sig, EffectCons m sig sigs sigl l)
    => [m a]
    -> m a
choose [] = failed
choose (p : ps) = foldr (?) p ps
{-# INLINE choose #-}

-- | Handle non-determinism effect with tree-based representation
runND
    :: (EffectMonad m sig sigs sigl (ListL l))
    => Prog (Sig (ND :+: sig) sigs sigl l) a
    -> m [a]
runND = unNDC . fold point con
{-# INLINE runND #-}

-- | Handle non-determinism effect using smart views
runNDSmart
    :: (EffectMonad m sig sigs sigl (ListL l))
    => SmartProg (Sig (ND :+: sig) sigs sigl l) a
    -> m [a]
runNDSmart = unNDC . smartFold point con
{-# INLINE runNDSmart #-}

-- | Handle non-determinism effect with 'Codensity' representation
runNDC :: (EffectMonad m sig sigs sigl (ListL l)) => Cod (NDC m) a -> m [a]
runNDC = unNDC . runCod var
{-# INLINE runNDC #-}

-- | Algebra for handling non-determinism effect
algND :: (Applicative m) => ND (m [a]) -> m [a]
algND Fail = pure []
algND (Or l r) = (++) <$> l <*> r

-- | 'TermAlgebra' instance for handling non-determinism effect
instance (EffectMonad m sig sigs sigl (ListL l)) => TermAlgebra (NDC m) (Sig (ND :+: sig) sigs sigl l) where
    con op = case op of
        A (Algebraic op') -> (wrap algND # (afwd . Algebraic)) op'
        S op' -> sfwd op'
        L op' -> lfwd op'
    {-# INLINE con #-}
    var = cc . point . point
    {-# INLINE var #-}

{- | Non-determinism carrier newtype

Combines other carrier types with '[]'.
-}
newtype NDC m a = NDC {unNDC :: m [a]} deriving (Functor)

{- | List lattice wrapper

Combines '[]' with a latent carrier @l@.
-}
newtype ListL l a = ListL {unListL :: [l a]}
    deriving (Show, Functor)

instance LCarrier ListL [] where
    concatM [] = pure []
    concatM [x] = x
    concatM (x : xs) = liftA2 (++) x (concatM xs)

instance Carrier NDC []
instance Forward 'Default NDC ListL

instance (Pointed m) => Pointed (NDC m) where
    point = NDC . point . point
    {-# INLINE point #-}