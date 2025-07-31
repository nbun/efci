{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
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
import Effect.FlatCurry.Constructor (
    CaseScope (..),
    ConsF,
    Value (..),
    lit,
    str2prog,
    val2str,
 )
import Effect.General.Memoization (Thunking)
import Effect.General.State (EffectCons, logCall)
import Free
import Signature

data IOAction a
    = PutChar Char a
    | GetChar (Char -> a)
    | ReadFile FilePath (String -> a)
    | WriteFile FilePath String a
    | AppendFile FilePath String a
    | IOError
    | Catch
    deriving (Functor)

putCharIO
    :: forall sig sigs sigl l m a
     . ( ConsF :<: sig
       , IOAction :<: sig
       , () :<<<: a
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl l
       )
    => m a
    -> m a
putCharIO x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f :: [Value ()] -> m a
    f [Lit (Charc c)] = injectA (PutChar c (return (injV ())))
{-# INLINE putCharIO #-}

writeFileIO
    , appendFileIO
        :: forall sig sigs sigl l m a
         . ( ConsF :<: sig
           , IOAction :<: sig
           , () :<<<: a
           , CaseScope :<: sigs
           , EffectCons m sig sigs sigl l
           )
        => m a
        -> m a
        -> m a
writeFileIO fp s = logCall >> injectS (External [fmap return fp, fmap return s] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv, sv] = injectA (WriteFile (val2str fpv) (val2str sv) (return (injV ())))
appendFileIO fp s = logCall >> injectS (External [fmap return fp, fmap return s] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv, sv] = injectA (AppendFile (val2str fpv) (val2str sv) (return (injV ())))
{-# INLINE writeFileIO #-}
{-# INLINE appendFileIO #-}

getCharIO :: (IOAction :<: sig, ConsF :<: sig, EffectCons m sig sigs sigl l) => m a
getCharIO = logCall >> injectA (GetChar (lit . Charc))
{-# INLINE getCharIO #-}

readFileIO
    :: forall sig sigs sigl m a
     . ( IOAction :<: sig
       , ConsF :<: sig
       , CaseScope :<: sigs
       , Thunking a :<<<<: sigl
       , EffectCons m sig sigs sigl Id
       )
    => m a
    -> m a
readFileIO fp = logCall >> injectS (External [fmap return fp] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv] = injectA (ReadFile (val2str fpv) str2prog)
{-# INLINE readFileIO #-}

runIO :: forall l a. Prog (Sig '[IOAction] '[] LVoid l) a -> IO a
runIO = unIOC . fold point con
{-# INLINE runIO #-}

runIOSmart :: forall l a. SmartProg (Sig '[IOAction] '[] LVoid l) a -> IO a
runIOSmart = unIOC . smartFold point con
{-# INLINE runIOSmart #-}

algIO :: IOAction (IO a) -> IO a
algIO (PutChar c k) = putChar c >> k
algIO (GetChar k) = getChar >>= k
algIO (WriteFile fp s k) = writeFile fp s >> k
algIO (ReadFile fp k) = readFile fp >>= k
algIO (AppendFile fp s k) = appendFile fp s >> k

instance TermAlgebra (IOC l) (Sig '[IOAction] '[] LVoid l) where
    con (A (Algebraic op)) = IOC . (algIO # absurd) . fmap unIOC $ op
    {-# INLINE con #-}
    var = IOC . return
    {-# INLINE var #-}

newtype IOC (l :: * -> *) a
    = IOC {unIOC :: IO a}
    deriving (Functor)

instance Pointed (IOC l) where
    point = IOC . return
    {-# INLINE point #-}

instance Pointed IO where
    point = return
    {-# INLINE point #-}
