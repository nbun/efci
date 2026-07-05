{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

{- |
Local binding effect

This module provides operations for creating and dereferencing
local bindings with lazy evaluation semantics.
-}
module Effect.FlatCurry.Let (let', lvar) where

import Effect.General.Memoization
import Effect.General.State
import Signature
import Type

{- | Dereference a variable by pointer

Returns the computation stored at the location defined by the t'Ptr' argument.
-}
lvar
    :: (EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => Ptr
    -> m a
lvar ptr = do
    logCall >> force ptr
{-# INLINE lvar #-}

{- | Create local bindings

* Takes a list of pointers (the variables to bind)
* Takes 'Args' containing the computations (or references) to bind
* Takes a computation to execute in the extended environment
* Returns the result of executing the computation
-}
let'
    :: forall m sig sigs sigl a
     . (EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => [Ptr]
    -> Args m a
    -> m a
    -> m a
let' [] _ e = e
let' vs args e =
    logCall >> case args of
        Progs ps -> mapM_ (uncurry thunk) (zip vs ps) >> e
        Thunks ptrs -> mapM_ (redirect @a) (zip vs ptrs) >> e
{-# INLINE let' #-}