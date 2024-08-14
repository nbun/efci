{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
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
import Debug (tracingActive)
import Free
import GHC.Stack (callStack, getCallStack)
import Signature
import Data.List (sortBy)

data StateF (tag :: Type) s a
    = Get (s -> a)
    | Put s a

instance Functor (StateF tag s) where
    fmap f (Get g) = Get (f . g)
    fmap f (Put s a) = Put s (f a)
    {-# INLINE fmap #-}

get
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => m s
get = logCallWith (identify @tag) >> injectA (Get @tag return)
{-# INLINE get #-}

put
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => s
    -> m ()
put s = logCallWith (identify @tag) >> injectA (Put @tag s (return ()))
{-# INLINE put #-}

modify
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => (s -> s)
    -> m ()
modify f =
    logCallWith (identify @tag) >> do
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
    :: (EffectCons m sig sigs sigl l, Renaming :<: sig)
    => Scope
    -> [VarIndex]
    -> m [VarIndex]
rename _ [] = logCall >> return []
rename scope vs =
    logCall >> do
        ((nextScope :: Scope, nextVar), renaming) <- get @Rename
        let end = nextVar + length vs - 1
        let vs' = [nextVar .. end]
        put @Rename ((nextScope, end + 1), addScope scope vs vs' ++ renaming)
        return vs'
{-# INLINE rename #-}

addScope
    :: Scope -> [VarIndex] -> [VarIndex] -> [((Scope, VarIndex), VarIndex)]
addScope scope vs vs' =
    let scopes = repeat scope
     in zip (zip scopes vs) vs'
{-# INLINE addScope #-}

freshNames
    :: (EffectCons m sig sigs sigl l, Renaming :<: sig)
    => Scope
    -> Int
    -> m [VarIndex]
freshNames _ 0 = logCall >> return []
freshNames scope n =
    logCall >> do
        ((nextScope :: Scope, nextVar), renaming) <- get @Rename
        let end = nextVar + n - 1
        let vs' = [nextVar .. end]
        put @Rename ((nextScope, end + 1), addScope scope vs' vs' ++ renaming)
        return vs'
{-# INLINE freshNames #-}

newScope
    :: (EffectCons m sig sigs sigl l, Renaming :<: sig)
    => m Scope
newScope =
    logCall >> do
        ((nextScope, newVar), renaming)
            :: ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)]) <-
            get @Rename
        put @Rename ((nextScope + 1, newVar), renaming)
        return nextScope
{-# INLINE newScope #-}

currentScope
    :: (EffectCons m sig sigs sigl l, Renaming :<: sig)
    => m Scope
currentScope =
    logCall >> do
        ((nextScope, _), _)
            :: ((Scope, VarIndex), [((Scope, VarIndex), VarIndex)]) <-
            get @Rename
        return (nextScope - 1)
{-# INLINE currentScope #-}

lookupRenaming
    :: (EffectCons m sig sigs sigl l, Renaming :<: sig)
    => Scope
    -> VarIndex
    -> m VarIndex
lookupRenaming scope i =
    logCall >> do
        (_ :: (Scope, VarIndex), renaming :: [((Scope, VarIndex), VarIndex)]) <-
            get @Rename
        case lookup (scope, i) renaming of
            Just i' -> return i'
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
     . s
    -> Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> Prog (Sig sig sigs sigl (StateL s l)) a
runState s = fmap snd . \p -> hState p s
{-# INLINE runState #-}

hState
    :: forall tag sig sigs sigl l s a
     . Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> (s -> Prog (Sig sig sigs sigl (StateL s l)) (s, a))
hState = unSTC . fold point con
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

-- Tracing

type TraceInfo = (String, String)

data Trace

instance Identify Trace where
    identify = "Trace"

type Tracing = StateF Trace [TraceInfo]

type EffectCons m sig sigs sigl l = (TermMonad m (Sig sig sigs sigl l), Tracing :<: sig, HasCallStack)

logCall :: (EffectCons m sig sigs sigl l) => m ()
logCall | tracingActive = let (_ : (name, _) : _) = getCallStack callStack in modifyWithoutLog ((name, "") :)
        | otherwise = return ()
           where
             modifyWithoutLog f = do
               s <- injectA (Get @Trace return)
               injectA (Put @Trace (f s) (return ()))
{-# INLINE logCall #-}

logCallWith :: (EffectCons m sig sigs sigl l) => String -> m ()
logCallWith s
    | tracingActive = let (_ : (name, _) : _) = getCallStack callStack in modifyWithoutLog ((name, s) :)
    | otherwise = return ()
      where
        modifyWithoutLog f = do
          s <- injectA (Get @Trace return)
          injectA (Put @Trace (f s) (return ()))
{-# INLINE logCallWith #-}

statistics :: [TraceInfo] -> [(TraceInfo, Int)]
statistics ti = sortBy (\(_,n) (_, m) -> compare n m) (foldr f [] ti)
  where
    f name acc =
        case lookup name acc of
            Just n -> (name, n + 1) : filter ((/= name) . fst) acc
            Nothing -> (name, 1) : acc
{-# INLINE statistics #-}