{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Effect.General.State where

import Curry.FlatCurry.Annotated.Type (Literal, QName, VarIndex)
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Debug (ctrace)
import Free
import Signature

data StateF (tag :: Type) s a
  = Get (s -> a)
  | Put s a

instance Functor (StateF tag s) where
  fmap f (Get g) = Get (f . g)
  fmap f (Put s a) = Put s (f a)
  {-# INLINE fmap #-}

get
  :: forall tag s m l sig sigs sigl
   . (EffectMonad m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
  => m s
get =
  ctrace ("get " ++ identify @tag) $ injectA (Get @tag return)
{-# INLINE get #-}

put
  :: forall tag s m l sig sigs sigl
   . (EffectMonad m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
  => s
  -> m ()
put s =
  ctrace ("put " ++ identify @tag) $
    injectA (Put @tag s (return ()))
{-# INLINE put #-}

modify
  :: forall tag s m l sig sigs sigl
   . (EffectMonad m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
  => (s -> s)
  -> m ()
modify f = do
  s <- get @tag
  put @tag (f s)
{-# INLINE modify #-}

class Identify a where
  identify :: String

data Rename

instance Identify Rename where
  identify = "Rename"

type Scope = Int

type Renaming =
  StateF Rename ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)])

rename
  :: (EffectMonad m sig sigs sigl l, Renaming :<: sig)
  => Scope
  -> [VarIndex]
  -> m [VarIndex]
rename scope vs = do
  ((nextScope :: Scope, nextVar), renaming) <- get @Rename
  let end = nextVar + length vs - 1
  let vs' = [nextVar .. end]
  ctrace
    ("rename " ++ show scope ++ " " ++ show vs ++ " to " ++ show vs')
    (return ())
  put @Rename ((nextScope, end + 1), addScope scope vs vs' ++ renaming)
  return vs'
{-# INLINE rename #-}

addScope
  :: Scope -> [VarIndex] -> [VarIndex] -> [((Scope, VarIndex), VarIndex)]
addScope scope vs vs' =
  let scopes = repeat scope
   in zip (zip scopes vs) vs'
{-# INLINE addScope #-}

fresh
  :: (EffectMonad m sig sigs sigl l, Renaming :<: sig)
  => Scope
  -> [VarIndex]
  -> m ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)])
fresh scope vs = do
  ((nextScope, nextVar), _ :: [((Scope, VarIndex), VarIndex)]) <- get @Rename
  let end = nextVar + length vs - 1
  let vs' = [nextVar .. end]
  ctrace
    ("rename " ++ show scope ++ " " ++ show vs ++ " to " ++ show vs')
    (return ())
  return ((nextScope, end + 1), addScope scope vs vs')
{-# INLINE fresh #-}

freshNames
  :: (EffectMonad m sig sigs sigl l, Renaming :<: sig)
  => Scope
  -> Int
  -> m [VarIndex]
freshNames scope n = do
  ((nextScope :: Scope, nextVar), renaming) <- get @Rename
  let end = nextVar + n - 1
  let vs' = [nextVar .. end]
  ctrace ("fresh " ++ show scope ++ " " ++ show vs') (return ())
  put @Rename ((nextScope, end + 1), addScope scope vs' vs' ++ renaming)
  return vs'
{-# INLINE freshNames #-}

newScope
  :: (EffectMonad m sig sigs sigl l, Renaming :<: sig)
  => m Scope
newScope = do
  ((nextScope, newVar), renaming)
    :: ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)]) <-
    get @Rename
  put @Rename ((nextScope + 1, newVar), renaming)
  ctrace ("newScope " ++ show nextScope) (return nextScope)
{-# INLINE newScope #-}

currentScope
  :: (EffectMonad m sig sigs sigl l, Renaming :<: sig)
  => m Scope
currentScope = do
  ((nextScope, _), _)
    :: ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)]) <-
    get @Rename
  ctrace ("currentScope " ++ show (nextScope - 1)) (return (nextScope - 1))
{-# INLINE currentScope #-}

lookupRenaming
  :: (EffectMonad m sig sigs sigl l, Renaming :<: sig)
  => Scope
  -> VarIndex
  -> m VarIndex
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
{-# INLINE lookupRenaming #-}

runState
  :: forall tag sig sigs sigl l s a
   . (Functor sig, Functor sigs)
  => s
  -> Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
  -> Prog (Sig sig sigs sigl (StateL s l)) a
runState s = fmap snd . \p -> hState p s
{-# INLINE runState #-}

hState
  :: forall tag sig sigs sigl l s a. (Functor sig, Functor sigs)
  => Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
  -> (s -> Prog (Sig sig sigs sigl (StateL s l)) (s, a))
hState = ctrace "runState" . unSTC . fold point con
{-# INLINE hState #-}

instance
  (EffectMonad m sig sigs sigl (StateL s l))
  => TermAlgebra (STC tag s m) (Sig (StateF tag s :+: sig) sigs sigl l)
  where
  con (A (Algebraic op)) = STC . (algS # afwd) . fmap unSTC $ op
   where
    algS (Get k) s = k s s
    algS (Put s' k) _ = k s'

    afwd op s = con (A (Algebraic (fmap (\k -> k s) op)))
  con (S (Enter op)) = STC $ \s -> con $ S $ Enter $ fmap (go s) op
   where
    go s hhx = do
      (s', hx) <- unSTC hhx s
      return (unSTC hx s')
  con (L (Node op l st k)) = STC $
    \s -> con $ L $ Node op (StateL (s, l)) (st' st) k'
   where
    st' st c (StateL (s', lv)) = StateL <$> unSTC (st c lv) s'
    k' (StateL (s', lv)) = unSTC (k lv) s'
  {-# INLINE con #-}
  var = STC . gen'State
   where
    gen'State x = return . (\s -> (s, x))
  {-# INLINE var #-}

runStateC
  :: forall tag m sig sigs sigl s l a
   . (EffectMonad m sig sigs sigl (StateL s l))
  => s
  -> Cod (STC tag s m) a
  -> m (s, a)
runStateC s p = unSTC (runCod var p) s
{-# INLINE runStateC #-}

runStateC'
  :: forall tag m sig sigs sigl s l a
   . (EffectMonad m sig sigs sigl (StateL s l))
  => s
  -> Cod (STC tag s m) a
  -> m a
runStateC' s p = snd <$> unSTC (runCod var p) s
{-# INLINE runStateC' #-}

newtype STC tag s m a = STC {unSTC :: s -> m (s, a)}

instance (Functor m) => Functor (STC tag s m) where
  fmap f (STC m) = STC (fmap (\(s', a) -> (s', f a)) . m)
  {-# INLINE fmap #-}

instance (Monad m) => Pointed (STC tag s m) where
  point x = STC (\s -> return (s, x))
  {-# INLINE point #-}

newtype StateL s l a = StateL {unStateL :: (s, l a)} deriving (Show)

instance (Functor l) => Functor (StateL s l) where
  fmap f (StateL (s, la)) = StateL (s, fmap f la)
  {-# INLINE fmap #-}

-- constraint store --

data CValue
  = VarC VarIndex
  | ConsC QName [VarIndex]
  | LitC Literal
  deriving (Show, Eq)

type Constraints = IntMap.IntMap CValue

lookupC :: VarIndex -> Constraints -> Maybe CValue
lookupC = IntMap.lookup
{-# INLINE lookupC #-}

addC :: VarIndex -> CValue -> Constraints -> Constraints
addC = IntMap.insert
{-# INLINE addC #-}

data CStore

instance Identify CStore where
  identify = "CStore"

type ConstraintStore = StateF CStore Constraints