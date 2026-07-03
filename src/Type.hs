{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}

{- | Core type definitions

This module provides the fundamental data types used throughout the interpreter,
including pointers, module representations, function declarations, and utility
functions for analyzing and manipulating FlatCurry programs.
-}
module Type (
    Ptr (..),
    AEFuncDecl (..),
    Module (..),
    fdclBody,
    Args (..),
    AEPattern (..),
    foldArgs,
    single,
    fdclBdy,
    reqFuncs,
    withoutTDecls,
    freshPtr,
    ptrKey,
    fdclName,
    mkPtr,
) where

import Curry.FlatCurry.Annotated.Type
import qualified Curry.FlatCurry.Type as CFT (OpDecl (..))
import Data.Map (Map)
import qualified Data.Set as Set
import GHC.Types.Unique (getKey)
import GHC.Types.Unique.Supply

-- | Find a function declaration by qualified name in a list of programs
findFDcl :: [AProg a] -> QName -> AFuncDecl a
findFDcl ps qn@(moduleName, _) = case res of
    Just fdecl -> fdecl
    Nothing -> error $ "Function declaration " ++ show qn ++ " not found"
  where
    res =
        foldr
            ( \(AProg name _ _ fdecls _) acc ->
                if name == moduleName
                    then findFuncDecl fdecls qn
                    else acc
            )
            Nothing
            ps

-- | Find a function declaration by qualified name in a list of function declarations
findFuncDecl :: [AFuncDecl a] -> QName -> Maybe (AFuncDecl a)
findFuncDecl fd qn = foldr (\fdecl acc -> if qn == funcName fdecl then Just fdecl else acc) Nothing fd
  where
    funcName (AFunc qn' _ _ _ _) = qn'

-- | Extract all function names from an expression
exprFuncs :: AExpr a -> [QName]
exprFuncs (AComb _ ct (f, _) args) =
    concatMap exprFuncs args ++ case ct of
        FuncCall -> [f]
        FuncPartCall _ -> [f]
        _ -> []
exprFuncs (AVar _ _) = []
exprFuncs (ALit _ _) = []
exprFuncs (ATyped _ e _) = exprFuncs e
exprFuncs (AOr _ e1 e2) = exprFuncs e1 ++ exprFuncs e2
exprFuncs (ALet _ bs e2) = concatMap (exprFuncs . snd) bs ++ exprFuncs e2
exprFuncs (ACase _ _ e alts) = exprFuncs e ++ concatMap (exprFuncs . (\(ABranch _ be) -> be)) alts
exprFuncs (AFree _ _ e) = exprFuncs e

-- | Extract all function names from a function declaration
declFuncs :: AFuncDecl a -> [QName]
declFuncs (AFunc _ _ _ _ e) = ruleFuncs e
  where
    ruleFuncs (ARule _ _ re) = exprFuncs re
    ruleFuncs (AExternal _ _) = []

{- | Extract required function declarations for a given expression

Returns programs containing only the functions needed to evaluate the expression
-}
reqFuncs :: forall a. [AProg a] -> AExpr a -> [AProg a]
reqFuncs ps e = reqFuncs' initial initial
  where
    initial = Set.fromList $ exprFuncs e

    reqFuncs' :: Set.Set QName -> Set.Set QName -> [AProg a]
    reqFuncs' acc new
        | Set.null new' = map (filterFuncs acc) ps
        | otherwise = reqFuncs' acc' new'
      where
        fset = Set.fromList $ concatMap (declFuncs . findFDcl ps) new
        new' = fset `Set.difference` acc
        acc' = acc `Set.union` fset

-- | Restrict a program to a set of qualified names
filterFuncs :: Set.Set QName -> AProg a -> AProg a
filterFuncs acc (AProg name imp tds fds ops) = AProg name imp tds fds' ops
  where
    fds' = filter (\(AFunc qn _ _ _ _) -> qn `elem` acc) fds

-- | Extract the body from a function declaration
fdclBdy :: AFuncDecl a -> AExpr a
fdclBdy (AFunc _ _ _ _ (ARule _ _ a)) = a
fdclBdy (AFunc _ _ _ _ (AExternal _ _)) = error "fdclBdy: external function has no body"

-- | Remove type declarations from a program, keeping only function declarations
withoutTDecls :: AProg a -> AProg a
withoutTDecls (AProg name imp _ fds ops) = AProg name imp [] fds ops

-- | Representation of a Curry module with type information and effect-based function declarations
data Module a
    = Module
        String
        [String]
        (Map QName TypeDecl)
        (Map QName (AEFuncDecl a))
        [CFT.OpDecl]
    deriving (Functor, Show)

-- | Annotated FlatCurry function declaration
data AEFuncDecl a = AEFunc QName Int Visibility TypeExpr a
    deriving (Functor, Show)

-- | Annotated branch expression for case analysis
data AEBranchExpr a = AEBranch (APattern a) (AExpr a)
    deriving (Show)

{- | Annotated pattern for pattern matching

* 'AEPattern': Constructor pattern with qualified name and pointer arguments
* 'AELPattern': Literal pattern
-}
data AEPattern
    = AEPattern QName [Ptr]
    | AELPattern Literal
    deriving (Show)

-- | Extract the body from a function declaration
fdclBody :: AEFuncDecl a -> a
fdclBody (AEFunc _ _ _ _ a) = a

-- | Extract the name from a function declaration
fdclName :: AEFuncDecl a -> QName
fdclName (AEFunc qn _ _ _ _) = qn

{- | Pointer type for referencing values in the heap

* Int: Unique identifier (needs to be an evaluated, boxed integer)
* String: Location information for debugging
-}
data Ptr = Ptr {-# NOUNPACK #-} Int String
    deriving (Eq, Ord, Show)

{- | Argument representation for function calls

* 'Progs': List of effect-based computations
* 'Thunks': List of references
-}
data Args m a = Progs [m a] | Thunks [Ptr]

-- | Wrap a single monadic computation in Progs
single :: m a -> Args m a
single x = Progs [x]

-- | Fold over 'Args', applying the appropriate function based on the constructor
foldArgs :: ([m a] -> b) -> ([Ptr] -> b) -> Args m a -> b
foldArgs f _ (Progs xs) = f xs
foldArgs _ g (Thunks xs) = g xs

-- | Create a fresh pointer using a unique supply and location string
freshPtr :: UniqSupply -> String -> (Ptr, UniqSupply)
freshPtr sup loc =
    let (!u, sup') = takeUniqFromSupply sup
        !i = fromIntegral (getKey u)
    in  (Ptr i loc, sup')
{-# INLINE freshPtr #-}

-- | Extract the integer key from a pointer
ptrKey :: Ptr -> VarIndex
ptrKey (Ptr i _) = i
{-# INLINE ptrKey #-}

-- | Create a pointer from an integer and location string
mkPtr :: Int -> String -> Ptr
mkPtr = Ptr
{-# INLINE mkPtr #-}
