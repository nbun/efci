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
{-# LANGUAGE BangPatterns #-}

module Effect.General.State where

import Curry.FlatCurry.Annotated.Type (Literal, QName, VarIndex)
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Data.List (sortBy)
import qualified Data.Map as Map
import Data.Unique (Unique)
import Debug (tracingActive)
import Debug.Trace (trace)
import Free
import GHC.Stack (callStack, getCallStack)
import GHC.Types.Unique
import GHC.Types.Unique.Supply
import Signature
import qualified Control.DeepSeq

data StateF (tag :: Type) s a
    = Get (s -> a)
    | Put s a
    | Modify (s -> s) a

instance Functor (StateF tag s) where
    fmap f (Get g) = Get (f . g)
    fmap f (Put s a) = Put s (f a)
    fmap f (Modify g a) = Modify g (f a)
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
put !s = logCallWith (identify @tag) >> injectA (Put @tag s (return ()))
{-# INLINE put #-}

modify
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => (s -> s)
    -> m ()
modify f =
    logCallWith (identify @tag) >> injectA (Modify @tag f (return ()))
{-# INLINE modify #-}

class Identify a where
    identify :: String

data Rename

instance Identify Rename where
    identify = "Rename"

type Renaming = StateF Rename RState

type RState = ([(VarIndex, VarIndex)], UniqSupply)

freshNames
    :: (EffectCons m sig sigs sigl l, Renaming :<: sig)
    => Int
    -> m [VarIndex]
freshNames 0 = logCall >> return []
freshNames n =
    logCall >> do
        (rs, sup) :: RState <- get @Rename
        let (vs', sup') = foldr (\_ (us, sup) -> let (u, sup') = takeUniqFromSupply sup in (fromIntegral (getKey u) : us, sup')) ([], sup) [1 .. n]
        put @Rename (rs, sup')
        return vs'
{-# INLINE freshNames #-}

modifyRenaming :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => ([(VarIndex, VarIndex)] -> [(VarIndex, VarIndex)]) -> m ()
modifyRenaming f =
    logCall >> do
        (rs, sup)
            :: RState <-
            get @Rename
        put @Rename (f rs, sup)
        return ()

lookupRenaming :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => VarIndex -> m VarIndex
lookupRenaming v =
    logCall >> do
        (rs, _) :: RState <- get @Rename
        case lookup v rs of
            Just v' -> return v'
            Nothing -> error $ "lookupRenaming: " ++ show v ++ " in "
{-# INLINE lookupRenaming #-}

rename :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => [VarIndex] -> m [VarIndex]
rename vs =
    logCall >> do
        (rs, sup) :: RState <- get @Rename
        let (rs', sup') = foldr (\v (us, sup) -> let (!u, sup') = takeUniqFromSupply sup in ((v, fromIntegral (getKey u)) : us, sup')) ([], sup) vs
        Control.DeepSeq.deepseq rs (put @Rename ((rs ++ rs', sup')))
        -- trace ("rename: " ++ show rs ++ show rs') $ return ()
        return (map snd rs')
{-# INLINE rename #-}

runState
    :: forall tag sig sigs sigl l s a
     . s
    -> Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> Prog (Sig sig sigs sigl (StateL s l)) a
runState s = fmap snd . \p -> hState p s
{-# INLINE runState #-}

runStateSmart
    :: forall tag sig sigs sigl l s a
     . s
    -> SmartProg (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> SmartProg (Sig sig sigs sigl (StateL s l)) a
runStateSmart s = fmap snd . \p -> hStateSmart p s
{-# INLINE runStateSmart #-}

hState
    :: forall tag sig sigs sigl l s a
     . Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> (s -> Prog (Sig sig sigs sigl (StateL s l)) (s, a))
hState = unSTC . fold point con
{-# INLINE hState #-}

hStateSmart
    :: forall tag sig sigs sigl l s a
     . SmartProg (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> (s -> SmartProg (Sig sig sigs sigl (StateL s l)) (s, a))
hStateSmart = unSTC . smartFold point con
{-# INLINE hStateSmart #-}

instance
    (EffectMonad m sig sigs sigl (StateL s l))
    => TermAlgebra (STC tag s m) (Sig (StateF tag s :+: sig) sigs sigl l)
    where
    con (A (Algebraic op)) = STC . (algS # afwd) . fmap unSTC $ op
      where
        algS (Get k) s = k s s
        algS (Put s' k) _ = k s'
        algS (Modify f k) s = k (f s)

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

type Constraints = Map.Map VarIndex CValue

lookupC :: VarIndex -> Constraints -> Maybe CValue
lookupC = Map.lookup
{-# INLINE lookupC #-}

addC :: VarIndex -> CValue -> Constraints -> Constraints
addC = Map.insert
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
logCall
    | tracingActive = let (_ : (name, _) : _) = getCallStack callStack in modifyWithoutLog ((name, "") :)
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
statistics ti = sortBy (\(_, n) (_, m) -> compare n m) (foldr f [] ti)
  where
    f name acc =
        case lookup name acc of
            Just n -> (name, n + 1) : filter ((/= name) . fst) acc
            Nothing -> (name, 1) : acc
{-# INLINE statistics #-}