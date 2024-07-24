{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda using `infix`" #-}

module Effect.General.State where

import Curry.FlatCurry.Annotated.Type (VarIndex)
import Data.Kind (Type)
import Debug (ctrace)
import Free
import Signature

data StateF (tag :: Type) s a
  = Get (s -> a)
  | Put s a
  deriving (Functor)

get
  :: forall tag s sig sigs sigl
   . (Functor sig, Functor sigs, Identify tag)
  => (StateF tag s :<: sig)
  => Prog (Sig sig sigs sigl Id) s
get =
  ctrace ("get " ++ identify @tag) $
    Call (A (Algebraic (inj (Get @tag return))))

put
  :: forall tag s sig sigs sigl
   . (Functor sig, Functor sigs, Identify tag)
  => (StateF tag s :<: sig)
  => s
  -> Prog (Sig sig sigs sigl Id) ()
put s =
  ctrace ("put " ++ identify @tag) $
    Call (A (Algebraic (inj (Put @tag s (return ())))))

modify
  :: forall tag s sig sigs sigl
   . (Functor sig, Functor sigs, Identify tag)
  => (StateF tag s :<: sig)
  => (s -> s)
  -> Prog (Sig sig sigs sigl Id) ()
modify f = do
  s <- get @tag
  put @tag (f s)

class Identify a where
  identify :: String

data Rename

instance Identify Rename where
  identify = "Rename"

type Scope = Int

type Renaming =
  StateF Rename ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)])

rename
  :: (Functor sig, Functor sigs, Renaming :<: sig)
  => Scope
  -> [VarIndex]
  -> Prog (Sig sig sigs sigl Id) [VarIndex]
rename scope vs = do
  ((nextScope :: Scope, nextVar), renaming) <- get @Rename
  let end = nextVar + length vs - 1
  let vs' = [nextVar .. end]
  ctrace
    ("rename " ++ show scope ++ " " ++ show vs ++ " to " ++ show vs')
    (return ())
  put @Rename ((nextScope, end + 1), addScope scope vs vs' ++ renaming)
  return vs'

addScope
  :: Scope -> [VarIndex] -> [VarIndex] -> [((Scope, VarIndex), VarIndex)]
addScope scope vs vs' =
  let scopes = repeat scope
   in zip (zip scopes vs) vs'

fresh
  :: (Functor sig, Functor sigs, Renaming :<: sig)
  => Scope
  -> [VarIndex]
  -> Prog
      (Sig sig sigs sigl Id)
      ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)])
fresh scope vs = do
  ((nextScope, nextVar), _ :: [((Scope, VarIndex), VarIndex)]) <- get @Rename
  let end = nextVar + length vs - 1
  let vs' = [nextVar .. end]
  ctrace
    ("rename " ++ show scope ++ " " ++ show vs ++ " to " ++ show vs')
    (return ())
  return ((nextScope, end + 1), addScope scope vs vs')

newScope
  :: (Functor sig, Functor sigs, Renaming :<: sig)
  => Prog (Sig sig sigs sigl Id) Scope
newScope = do
  ((nextScope, newVar), renaming)
    :: ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)]) <-
    get @Rename
  put @Rename ((nextScope + 1, newVar), renaming)
  ctrace ("newScope " ++ show nextScope) (return nextScope)

currentScope
  :: (Functor sig, Functor sigs, Renaming :<: sig)
  => Prog (Sig sig sigs sigl Id) Scope
currentScope = do
  ((nextScope, _), _)
    :: ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)]) <-
    get @Rename
  ctrace ("currentScope " ++ show (nextScope - 1)) (return (nextScope - 1))

lookupRenaming
  :: (Functor sig, Functor sigs, Renaming :<: sig)
  => Scope
  -> VarIndex
  -> Prog (Sig sig sigs sigl Id) VarIndex
lookupRenaming scope i = do
  (_ :: (Scope, VarIndex), renaming :: [((Scope, VarIndex), VarIndex)]) <-
    get @Rename
  case lookup (scope, i) renaming of
    Just i' ->
      ctrace
        ( "lookupRenaming: "
            ++ show scope
            ++ " "
            ++ show i
            ++ " "
            ++ show i'
            ++ " "
            ++ show renaming
        )
        return
        i'
    Nothing ->
      error $
        "lookupRenaming: "
          ++ show scope
          ++ " "
          ++ show i
          ++ " not found in "
          ++ show renaming

runState
  :: forall tag sig sigs sigl l s a
   . (Functor sig, Functor sigs)
  => s
  -> Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl (StateL s l)) a
runState s = fmap snd . \p -> hState p s

hState
  :: (Functor sig, Functor sigs)
  => Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
  -> (s -> Prog (Sig sig sigs sigl (StateL s l)) (s, a))
hState = ctrace "runState" . unST . fold point (aalg algST)
 where
  algST :: StateF tag s (ST s sig sigs sigl l x) -> ST s sig sigs sigl l x
  algST (Get k) = ST (\s -> unST (k s) s)
  algST (Put s' k) = ST (\_ -> unST k s')

instance Forward (ST s) where
  afwd op = ST (\s -> Call (A (Algebraic (fmap (\k -> unST k s) op))))
  sfwd op = ST $ \s -> Call $ S $ Enter $ fmap (go s) op
   where
    go s hhx = do
      (s', hx) <- unST hhx s
      return (unST hx s')
  lfwd op l st k = ST $ \s -> Call $ L $ Node op (StateL (s, l)) st' k'
   where
    st' c (StateL (s', lv)) = StateL <$> unST (st c lv) s'
    k' (StateL (s', lv)) = unST (k lv) s'

newtype ST s sig sigs sigl l a = ST {unST :: s -> Prog (Sig sig sigs sigl (StateL s l)) (s, a)}
  deriving (Functor)

instance (Functor sig, Functor sigs) => Pointed (ST s sig sigs sigl l) where
  point x = ST $ \s -> return (s, x)

newtype StateL s l a = StateL {unStateL :: (s, l a)} deriving (Show)

instance (Functor l) => Functor (StateL s l) where
  fmap f (StateL (s, la)) = StateL (s, fmap f la)