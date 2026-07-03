{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{- | IO effect

This module provides an effect for input/output operations.

Note that this effect cannot be modularly combined, as we cannot forward
other effects' semantics through IO. Hence, the IO effect always needs to be
run last in a handler pipeline.
-}
module Effect.FlatCurry.IO (
    IOAction,
    getCharIO,
    putCharIO,
    writeFileIO,
    appendFileIO,
    readFileIO,
    IOC (..),
    runIO,
    runIOSmart,
) where

import Curry.FlatCurry.Type (Literal (..))
import Data.Kind (Type)
import Effect.FlatCurry.Constructor (
    Match (..),
    Term,
    Value (..),
    lit,
    str2prog,
    unit,
    val2str,
 )
import Effect.General.Memoization (Thunking)
import Effect.General.State (EffectCons, logPrimCall)
import Free
import Signature

{- | IO effect operations

* 'PutChar': Output a character
* 'GetChar': Input a character
* 'ReadFile': Read a file
* 'WriteFile': Write to a file
* 'AppendFile': Append to a file
-}
data IOAction a
    = PutChar Char a
    | GetChar (Char -> a)
    | ReadFile FilePath (String -> a)
    | WriteFile FilePath String a
    | AppendFile FilePath String a
    deriving
        ( Functor
        )

{- | Output a character to stdout

Evaluates a computation to a character and produces a computation that outputs it.
-}
putCharIO
    :: forall sig sigs sigl l m a
     . ( Term :<: sig
       , IOAction :<: sig
       , Match :<: sigs
       , EffectCons m sig sigs sigl l
       )
    => m a
    -> m a
putCharIO x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f :: [Value ()] -> m a
    f [Lit (Charc c)] = injectA (PutChar c unit)
{-# INLINE putCharIO #-}

{- | Write a string to a file

Evaluates file path and string computations and produces a computation that writes the string to the file.
-}
writeFileIO
    , appendFileIO
        :: forall sig sigs sigl l m a
         . ( Term :<: sig
           , IOAction :<: sig
           , Match :<: sigs
           , EffectCons m sig sigs sigl l
           )
        => m a
        -> m a
        -> m a
writeFileIO fp s = logPrimCall >> injectS (Match [fmap return fp, fmap return s] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv, sv] = injectA (WriteFile (val2str fpv) (val2str sv) unit)
{-# INLINE writeFileIO #-}

{- | Append a string to a file

Evaluates file path and string computations and produces a computation that appends the string to the file.
-}
appendFileIO fp s = logPrimCall >> injectS (Match [fmap return fp, fmap return s] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv, sv] = injectA (AppendFile (val2str fpv) (val2str sv) unit)
{-# INLINE appendFileIO #-}

{- | Input a character from stdin

Performs a getChar IO action and produces a computation that wraps the result in a character literal.
-}
getCharIO :: (IOAction :<: sig, Term :<: sig, EffectCons m sig sigs sigl l) => m a
getCharIO = logPrimCall >> injectA (GetChar (lit . Charc))
{-# INLINE getCharIO #-}

{- | Read the contents of a file

Evaluates a file path computation and produces a computation that returns the file contents as a string.
-}
readFileIO
    :: forall sig sigs sigl m a
     . ( IOAction :<: sig
       , Term :<: sig
       , Match :<: sigs
       , Thunking a :<<: sigl
       , EffectCons m sig sigs sigl Id
       )
    => m a
    -> m a
readFileIO fp = logPrimCall >> injectS (Match [fmap return fp] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv] = injectA (ReadFile (val2str fpv) str2prog)
{-# INLINE readFileIO #-}

-- | Handle IO effect with tree-based representation
runIO :: forall l a. Prog (Sig '[IOAction] '[] LVoid l) a -> IO a
runIO = unIOC . fold point con
{-# INLINE runIO #-}

-- | Handle IO effect using smart views
runIOSmart :: forall l a. SmartProg (Sig '[IOAction] '[] LVoid l) a -> IO a
runIOSmart = unIOC . smartFold point con
{-# INLINE runIOSmart #-}

-- | Algebra for handling IO effect
algIO :: IOAction (IO a) -> IO a
algIO (PutChar c k) = putChar c >> k
algIO (GetChar k) = getChar >>= k
algIO (WriteFile fp s k) = writeFile fp s >> k
algIO (ReadFile fp k) = readFile fp >>= k
algIO (AppendFile fp s k) = appendFile fp s >> k

-- | 'TermAlgebra' instance for handling IO effect
instance TermAlgebra (IOC l) (Sig '[IOAction] '[] LVoid l) where
    con (A (Algebraic op)) = IOC . (algIO # absurd) . fmap unIOC $ op
    {-# INLINE con #-}
    var = IOC . return
    {-# INLINE var #-}

{- | IO carrier newtype

Note that 'IO' cannot be modularly combined with other carriers, as evidenced
by the phantom type @m@.
-}
newtype IOC (m :: Type -> Type) a
    = IOC {unIOC :: IO a}
    deriving (Functor)

instance Pointed (IOC l) where
    point = IOC . return
    {-# INLINE point #-}