{-# LANGUAGE AllowAmbiguousTypes #-}
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
{-# LANGUAGE EmptyCase #-}

module Effect.FlatCurry.IO where

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


putCharIO :: forall sig sigs sigl l m a. ( ConsF :<: sig
             , IOAction :<: sig
             , () :<<<: a
             , CaseScope :<: sigs
             , EffectMonad m sig sigs sigl l)
          => m a
          -> m a
putCharIO x = injectS (External [fmap return x] (return . f))
  where
    f :: [Value ()] -> m a
    f [Lit (Charc c)] = injectA (PutChar c (return (injV ())))
{-# INLINE putCharIO #-}

writeFileIO, appendFileIO :: forall sig sigs sigl l m a. ( ConsF :<: sig
               , IOAction :<: sig
               , () :<<<: a
               , CaseScope :<: sigs
               ,  EffectMonad m sig sigs sigl l)
            => m a
            -> m a
            -> m a
writeFileIO fp s = injectS (External [fmap return fp, fmap return s] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv, sv] = injectA (WriteFile (val2str fpv) (val2str sv) (return (injV ())))

appendFileIO fp s = injectS (External [fmap return fp, fmap return s] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv, sv] = injectA (AppendFile (val2str fpv) (val2str sv) (return (injV ())))
{-# INLINE writeFileIO #-}
{-# INLINE appendFileIO #-}

getCharIO :: (IOAction :<: sig, ConsF :<: sig, EffectMonad m sig sigs sigl l) => m a
getCharIO = injectA (GetChar (lit . Charc))
{-# INLINE getCharIO #-}

readFileIO :: forall sig sigs sigl m a. ( IOAction :<: sig
              , ConsF :<: sig
              , CaseScope :<: sigs
              , Thunking a :<<<<: sigl
              , EffectMonad m sig sigs sigl Id)
           => m a
           -> m a
readFileIO fp = injectS (External [fmap return fp] (return . f))
  where
    f :: [Value ()] -> m a
    f [fpv] = injectA (ReadFile (val2str fpv) str2prog)
{-# INLINE readFileIO #-}

runIO :: forall l a. Prog (Sig IOAction Void LVoid l) a -> IO a
runIO = unIOC . fold point con
{-# INLINE runIO #-}

instance TermAlgebra (IOC l) (Sig IOAction Void LVoid l) where
  con (A (Algebraic op)) = IOC . algIO . fmap unIOC $ op
    where
      algIO (PutChar c k) = putChar c >> k
      algIO (GetChar k) = getChar >>= k
      algIO (WriteFile fp s k) = writeFile fp s >> k
      algIO (ReadFile fp k) = readFile fp >>= k
      algIO (AppendFile fp s k) = appendFile fp s >> k
  con (S (Enter op)) = case op of
  con (L (Node op _ _ _)) = case op of
  {-# INLINE con #-}
  var = IOC . gen'IO
    where gen'IO = return
  {-# INLINE var #-}

newtype IOC (l :: * -> *) a =
  IOC { unIOC :: IO a }
  deriving (Functor)

instance Pointed (IOC l) where
  point = IOC . return
  {-# INLINE point #-}

instance Pointed IO where
  point = return
  {-# INLINE point #-}
