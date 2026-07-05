{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{- | Declaration effect

This module provides an effect for retrieving function declarations
from the source program and for initializing the internal representation
of the source program.
-}
module Effect.FlatCurry.Declarations (
    DeclF (..),
    getBody,
    DC,
    runDecl,
    initDecls,
    runDeclSmart,
    runDeclC,
    Progs (..),
) where

import Control.Monad (void)
import Curry.FlatCurry.Annotated.Type (QName)
import Data.Kind (Type)
import qualified Data.Map as Map
import Effect.General.State (EffectCons, logPrimCall)
import Forwarding
import Free
import Signature
import Type (AEFuncDecl, Module (..), fdclBody, fdclName)

{- | Declaration effect operations

* 'DeclBody': Retrieve the body of a defined function
* 'Init': Initialize the handler's list of source modules
-}
data DeclF v :: Type -> (Type -> Type) -> Type where
    DeclBody :: QName -> DeclF v v NoSub
    Init :: [Module ()] -> DeclF v () (ManySub v)

{- | Type for representing multiple subcomputations with latent effects

Used for storing multiple subcomputations within an operation.
-}
data ManySub v :: Type -> Type where
    -- | Represents a single substructural element identified by QName
    Many :: QName -> ManySub v v

{- | Wrapper for lists of effect-based modules

Contains a list of modules with effect-based function bodies.
-}
newtype Progs (l :: Type -> Type) (v :: Type) (m :: Type -> Type) = Progs {unProgs :: [Module (l () -> DC (Progs l v m) m (l v))]}

{- | Get the body of a declared function

Looks up a function by qualified name and returns its body as a computation
-}
getBody
    :: forall sig sigs sigl m a
     . (EffectCons m sig sigs sigl Id)
    => (DeclF a :<<: sigl)
    => QName -> m a
getBody qn = logPrimCall >> injectL (DeclBody qn :: DeclF a a NoSub) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE getBody #-}

{- | Initialize the declaration store with a list of modules

Processes all function declarations from the modules and makes them available
for lookup during program execution
-}
initDecls
    :: forall sig sigs sigl m v
     . (DeclF v :<<: sigl, EffectCons m sig sigs sigl Id)
    => [Module (m v)] -> m ()
initDecls ps = logPrimCall >> injectL (Init (map void ps) :: DeclF v () (ManySub v :: Type -> Type)) (Id ()) (\(Many qn) _ -> fmap Id (fdclBody $ moduleLookup ps qn)) (const (return ()))
{-# INLINE initDecls #-}

{- | Declaration carrier newtype

Wraps a computation that depends on program declarations.
-}
newtype DC r m a = DC {unDC :: r -> m a}

instance (Functor m) => Functor (DC (Progs l v m) m) where
    fmap f (DC x) = DC $ \th -> fmap f (x th)
    {-# INLINE fmap #-}

-- | Handle declarations effect with tree-based representation
runDecl :: (EffectMonad m sig sigs sigl l) => Progs l v m -> Prog (Sig sig sigs (DeclF v :+++: sigl) l) a -> m a
runDecl s p = hDecl p s
{-# INLINE runDecl #-}

{- | Handle declarations effect with tree-based representation

This is a version of 'runDecl' with flipped order of arguments.
-}
hDecl
    :: (EffectMonad m sig sigs sigl l)
    => Prog (Sig sig sigs (DeclF v :+++: sigl) l) a
    -> Progs l v m
    -> m a
hDecl = unDC . fold point con
{-# INLINE hDecl #-}

-- | Handle declarations effect using smart views
runDeclSmart :: (EffectMonad m sig sigs sigl l) => Progs l v m -> SmartProg (Sig sig sigs (DeclF v :+++: sigl) l) a -> m a
runDeclSmart s p = hDeclSmart p s
{-# INLINE runDeclSmart #-}

-- | This is a version of 'runDeclSmart' with flipped order of arguments.
hDeclSmart
    :: (EffectMonad m sig sigs sigl l)
    => SmartProg (Sig sig sigs (DeclF v :+++: sigl) l) a
    -> Progs l v m
    -> m a
hDeclSmart = unDC . smartFold point con
{-# INLINE hDeclSmart #-}

-- | Handle declarations effects with Codensity representation
runDeclC :: (EffectMonad m sig sigs sigl l) => Progs l v m -> Cod (DC (Progs l v m) m) a -> m a
runDeclC th p = unDC (runCod var p) th
{-# INLINE runDeclC #-}

-- | Merge static module information with effect-based function bodies
mergeModule
    :: (ManySub v v -> l () -> DC (Progs l v m) m (l v))
    -> Module ()
    -> Module (l () -> DC (Progs l v m) m (l v))
mergeModule get (Module name imps tds fds opds) = Module name imps tds fds' opds
  where
    fds' = Map.map (\fdecl -> get (Many (fdclName fdecl)) <$ fdecl) fds

instance ReaderCarrier (DC (Progs l v m)) (Progs l v m)
instance Forward 'Reader (DC (Progs l v m)) VoidL

-- | Algebra for handling declarations effect
algDecl
    :: (Monad m)
    => Latent (DeclF v) l (DC (Progs l v m) m) (DC (Progs l v m) m a)
    -> DC (Progs l v m) m a
algDecl (Node op l st' k') = DC $ \th ->
    let k = unDC . k'
    in  case op of
            DeclBody qn -> do
                lv <- (unDC . fdclBody (moduleLookup (unProgs th) qn)) l th
                k lv th
            Init ms -> k l (Progs $ map (mergeModule st') ms)

-- | 'TermAlgebra' instance for handling declarations effect
instance (EffectMonad m sig sigs sigl l) => TermAlgebra (DC (Progs l v m) m) (Sig sig sigs (DeclF v :+++: sigl) l) where
    con (A op) = afwd @VoidL op
    con (S op) = sfwd @VoidL op
    con (L (Node op l st k)) = case op of
        (Inl3 op') -> algDecl (Node op' l st k)
        (Inr3 op') -> lfwd @VoidL @'Reader (Node op' l st k)
    {-# INLINE con #-}
    var = DC . (\x _ -> return x)
    {-# INLINE var #-}

instance (Pointed m) => Pointed (DC (Progs l v m) m) where
    point x = DC $ \_ -> point x
    {-# INLINE point #-}

{- | Helper function for retrieving a function declaration from a list of modules

Produces an error if a function declaration cannot be found within the list of modules.
-}
moduleLookup :: [Module a] -> QName -> AEFuncDecl a
moduleLookup [] qn = error $ "Function declaration not found: " ++ show qn
moduleLookup (Module name _ _ fdecls _ : ms) qn@(moduleName, _)
    | name == moduleName = case Map.lookup qn fdecls of
        Just fdcl -> fdcl
        Nothing -> error $ "Function " ++ show qn ++ "missing from module " ++ show moduleName
    | otherwise = moduleLookup ms qn