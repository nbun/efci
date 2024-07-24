{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Type where

import Curry.FlatCurry.Type (
  QName,
  TypeDecl (..),
  TypeExpr (..),
  VarIndex,
  Visibility (..),
 )
import qualified Curry.FlatCurry.Type as CFT (OpDecl (..))
import Data.Map (Map)

data AEProg a
  = AEProg
      String
      [String]
      (Map QName TypeDecl)
      (Map QName (AEFuncDecl a))
      [CFT.OpDecl]
  deriving (Functor, Show)

data AEFuncDecl a = AEFunc QName Int Visibility TypeExpr (AERule a)
  deriving (Functor, Show)

data AERule a
  = AERule [VarIndex] a
  | AEExternal String
  deriving (Functor, Show)