{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Effect.General.State (
    EffectCons,
    logCall,
    StateL (..),
    Renaming,
    ConstraintStore,
    CStore,
    CValue (..),
    freshNames,
    modify,
    addC,
    get,
    lookupC,
    logCallWith,
    newRenamingScope,
    put,
    StateF,
    Trace,
    TraceInfo,
    Constraints,
    Rename,
    RState,
    STC,
    statistics,
    hState,
    runState,
    initRenaming,
    hStateSmart,
    runStateSmart,
    runStateC,
    runStateC',
    lookupRenaming,
    rename,
    getCurrentQName,
    prettyTI,
    logPrimCall,
) where

import Curry.FlatCurry.Annotated.Type (Literal, QName, VarIndex)
import Data.Kind (Type)
import Data.List (sortBy, partition)
import qualified Data.Map as Map
import Debug (tracingActive)
import Free
import GHC.Stack (callStack, getCallStack)
import GHC.Types.Unique
import GHC.Types.Unique.Supply
import Signature
import Type (Ptr (..), mkPtr)

data StateF (tag :: Type) s a
    = Get (s -> a)
    | Modify (s -> s) a
    deriving (Functor)

get
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => m s
get = logCallWith (identify @tag) True >> injectA (Get @tag return)
{-# INLINE get #-}

put
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => s
    -> m ()
put s = logCallWith (identify @tag) False >> modify @tag (const s)
{-# INLINE put #-}

modify
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => (s -> s)
    -> m ()
modify f =
    logCallWith (identify @tag) True >> injectA (Modify @tag f (return ()))
{-# INLINE modify #-}

class Identify a where
    identify :: String

data Rename

instance Identify Rename where
    identify = "Rename"

initRenaming :: UniqSupply -> RState
initRenaming sup = RState [] sup Nothing

type Renaming = StateF Rename RState

data RState = RState {renaming :: [(VarIndex, Ptr)], supply :: !UniqSupply, currentQName :: Maybe QName}

instance Show RState where
    show _ = "RState"

freshNames
    :: (EffectCons m sig sigs sigl l, Renaming :<: sig)
    => Int
    -> m [Ptr]
freshNames 0 = return []
freshNames n =
    logCall >> do
        r <- get @Rename
        let (!vs', sup') = renameFromSupply (Just ("generated", "")) (replicate n (-1)) (supply r)
        put @Rename (r{supply = sup'})
        return vs'
{-# INLINE freshNames #-}

newRenamingScope :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => QName -> m ()
newRenamingScope qn =
    logCall >> modify @Rename (\r -> r{renaming = [], currentQName = Just qn})
{-# INLINE newRenamingScope #-}

getCurrentQName :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => m (Maybe QName)
getCurrentQName = logCall >> fmap currentQName (get @Rename)
{-# INLINE getCurrentQName #-}

lookupRenaming :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => VarIndex -> m Ptr
lookupRenaming v =
    logCall >> do
        r <- get @Rename
        case lookup v (renaming r) of
            Just !v' -> return v'
            Nothing -> error $ "lookupRenaming: " ++ show v ++ " in "
{-# INLINE lookupRenaming #-}

rename :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => [VarIndex] -> m [Ptr]
rename vs =
    logCall >> do
        r <- get @Rename
        let (vs', sup') = renameFromSupply (currentQName r) vs (supply r)
        put @Rename (r{renaming = renaming r ++ zip vs vs', supply = sup'})
        return vs'
{-# INLINE rename #-}

renameFromSupply :: Maybe QName -> [VarIndex] -> UniqSupply -> ([Ptr], UniqSupply)
renameFromSupply _ [] sup = ([], sup)
renameFromSupply mqn (v:vs) sup =
    let (!u, sup') = takeUniqFromSupply sup
        !i = fromIntegral (getKey u)
        (is, sup'') = renameFromSupply mqn vs sup'
        loc = case mqn of
                Just (mdl, fn) -> mdl ++ "." ++ fn ++ " " ++ show v
                Nothing -> show v
     in (mkPtr i loc : is, sup'')

runState
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => s
    -> Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> m a
runState s = fmap snd . \p -> hState p s
{-# INLINE runState #-}

runStateSmart
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => s
    -> SmartProg (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> m a
runStateSmart s = fmap snd . \p -> hStateSmart p s
{-# INLINE runStateSmart #-}

hState
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> (s -> m (s, a))
hState = unSTC . fold point con
{-# INLINE hState #-}

hStateSmart
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => SmartProg (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> (s -> m (s, a))
hStateSmart = unSTC . smartFold point con
{-# INLINE hStateSmart #-}

instance StateCarrier (STC tag s) s
instance Forward 'State (STC tag s) (StateL s)
instance LCarrier (StateL s) ((,) s) where
    concatM (_, x) = x

algS :: StateF tag s (s -> m a) -> s -> m a
algS (Get k) s = k s s
algS (Modify f k) s = k (f s)

instance
    (EffectMonad m sig sigs sigl (StateL s l))
    => TermAlgebra (STC tag s m) (Sig (StateF tag s :+: sig) sigs sigl l)
    where
    con (A (Algebraic op)) = (wrapst algS # (afwd . Algebraic)) op
    con (S op) = sfwd op
    con (L op) = lfwd op
    {-# INLINE con #-}
    var = STC . \x -> point . (,x)
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
    deriving (Functor)

instance (Pointed m) => Pointed (STC tag s m) where
    point x = STC (\s -> point (s, x))
    {-# INLINE point #-}

newtype StateL s l a = StateL {unStateL :: (s, l a)}
    deriving (Functor, Show)

-- constraint store --

data CValue
    = VarC Ptr
    | ConsC QName [Ptr]
    | LitC Literal
    deriving (Show, Eq)

type Constraints = Map.Map Ptr CValue

lookupC :: Ptr -> Constraints -> Maybe CValue
lookupC = Map.lookup
{-# INLINE lookupC #-}

addC :: Ptr -> CValue -> Constraints -> Constraints
addC = Map.insert
{-# INLINE addC #-}

data CStore

instance Identify CStore where
    identify = "CStore"

type ConstraintStore = StateF CStore Constraints

-- Tracing
data TraceInfo = TI {opName :: String, details :: String, primOp :: Bool}
  deriving (Eq, Ord, Show)

prettyTI :: TraceInfo -> String
prettyTI (TI op dtls _) | dtls == "" = op
                        | otherwise = op ++ " (" ++ dtls ++ ")"

data Trace

instance Identify Trace where
    identify = "Trace"

type Tracing = StateF Trace [TraceInfo]

type EffectCons m sig sigs sigl l = (TermMonad m (Sig sig sigs sigl l), Tracing :<: sig, HasCallStack)

logPrimCall :: (EffectCons m sig sigs sigl l) => m ()
logPrimCall
    | tracingActive = case getCallStack callStack of
                        (_ : (name, _) : _)  -> modifyWithoutLog (TI name "" True :)
                        _ -> return ()
    | otherwise = return ()
  where
    modifyWithoutLog f = injectA (Modify @Trace f (return ()))
{-# INLINE logPrimCall #-}

logCall :: (EffectCons m sig sigs sigl l) => m ()
logCall
    | tracingActive = case getCallStack callStack of
                        (_ : (name, _) : _)  -> modifyWithoutLog (TI name "" False :)
                        _ -> return ()
    | otherwise = return ()
  where
    modifyWithoutLog f = injectA (Modify @Trace f (return ()))
{-# INLINE logCall #-}

logCallWith :: (EffectCons m sig sigs sigl l) => String -> Bool -> m ()
logCallWith s prim
    | tracingActive = case getCallStack callStack of
                        (_ : (name, _) : _)  -> modifyWithoutLog (TI name s prim :)
                        _ -> return ()
    | otherwise = return ()
  where
    modifyWithoutLog f = injectA (Modify @Trace f (return ()))
{-# INLINE logCallWith #-}

statistics :: [TraceInfo] -> ([(TraceInfo, Int)], [(TraceInfo, Int)])
statistics ti = (sortedCount prims, sortedCount comb)
  where
    (prims, comb) = partition primOp ti
    sortedCount = sortBy (\(_, n) (_, m) -> compare n m) . count
    count = Map.toList . Map.fromListWith (+) . map (,1)
{-# INLINE statistics #-}