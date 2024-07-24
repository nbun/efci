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

putCharIO
  :: ( ConsF :<: sig
     , Functor sig
     , Functor sigs
     , IOAction :<: sig
     , () :<<<: a
     , CaseScope :<: sigs
     )
  => Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
putCharIO x = Call (S (Enter (inj (External [fmap return x] (return . f)))))
 where
  f [Lit (Charc c)] =
    Call
      (A (Algebraic (inj (PutChar c (return (injV ()))))))

writeFileIO
  , appendFileIO
    :: ( ConsF :<: sig
       , Functor sig
       , Functor sigs
       , IOAction :<: sig
       , () :<<<: a
       , CaseScope :<: sigs
       )
    => Prog (Sig sig sigs sigl Id) a
    -> Prog (Sig sig sigs sigl Id) a
    -> Prog (Sig sig sigs sigl Id) a
writeFileIO fp s =
  Call
    (S (Enter (inj (External [fmap return fp, fmap return s] (return . f)))))
 where
  f [fpv, sv] =
    Call $
      A
        ( Algebraic
            (inj (WriteFile (val2str fpv) (val2str sv) (return (injV ()))))
        )
appendFileIO fp s =
  Call
    (S (Enter (inj (External [fmap return fp, fmap return s] (return . f)))))
 where
  f [fpv, sv] =
    Call $
      A
        ( Algebraic
            (inj (AppendFile (val2str fpv) (val2str sv) (return (injV ()))))
        )

getCharIO :: (IOAction :<: sig, ConsF :<: sig) => Prog (Sig sig sigs sigl Id) a
getCharIO = Call (A (Algebraic (inj (GetChar c2l))))
 where
  c2l c = lit (Charc c)

readFileIO
  :: ( IOAction :<: sig
     , ConsF :<: sig
     , CaseScope :<: sigs
     , Thunking a :<<<<: sigl
     , Functor sig
     , Functor sigs
     )
  => Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
readFileIO fp = Call (S (Enter (inj (External [fmap return fp] (return . f)))))
 where
  f [fpv] = Call (A (Algebraic (inj (ReadFile (val2str fpv) str2prog))))

runIO :: forall l a. Prog (Sig IOAction Void LVoid l) a -> IO a
runIO = fold point alg
 where
  alg (A (Algebraic op)) = algIO op
   where
    algIO :: IOAction (IO x) -> IO x
    algIO (PutChar c k) = putChar c >> k
    algIO (GetChar k) = getChar >>= k
    algIO (WriteFile fp s k) = writeFile fp s >> k
    algIO (ReadFile fp k) = readFile fp >>= k
    algIO (AppendFile fp s k) = appendFile fp s >> k

instance Pointed IO where
  point = return
