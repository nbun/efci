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

{- | State effect

This module contains the state effect and specialized versions
of it for storing constraints, renaming, and tracing operations.
-}
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
import Data.List (partition, sortBy)
import qualified Data.Map as Map
import Debug (tracingActive)
import Forwarding
import Free
import GHC.Stack (callStack, getCallStack)
import GHC.Types.Unique
import GHC.Types.Unique.Supply
import Signature
import Type (Ptr (..), mkPtr)

{- | State effect for generic state operations

* 'Get': Retrieve the current state and compute a result
* 'Modify': Update the state using a transformation function and compute a result
-}
data StateF (tag :: Type) s a
    = Get (s -> a)
    | Modify (s -> s) a
    deriving (Functor)

-- | Get the current state
get
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => m s
get = logCallWith (identify @tag) True >> injectA (Get @tag return)
{-# INLINE get #-}

{- | Put a new state

Replaces the current state with a new value.
-}
put
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => s
    -> m ()
put s = logCallWith (identify @tag) False >> modify @tag (const s)
{-# INLINE put #-}

{- | Modify the current state

Applies a transformation function to the current state.
-}
modify
    :: forall tag s m l sig sigs sigl
     . (EffectCons m sig sigs sigl l, Identify tag, StateF tag s :<: sig)
    => (s -> s)
    -> m ()
modify f =
    logCallWith (identify @tag) True >> injectA (Modify @tag f (return ()))
{-# INLINE modify #-}

{- | Handle state effect with tree-based representation

This is a version of 'hState' that omits the final state.
-}
runState
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => s
    -> Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> m a
runState s = fmap snd . \p -> hState p s
{-# INLINE runState #-}

-- | Handle state effect with tree-based representation
hState
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => Prog (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> (s -> m (s, a))
hState = unSTC . fold point con
{-# INLINE hState #-}

{- | Handle state effect using smart views

This is a version of 'hStateSmart' that omits the final state.
-}
runStateSmart
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => s
    -> SmartProg (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> m a
runStateSmart s = fmap snd . \p -> hStateSmart p s
{-# INLINE runStateSmart #-}

-- | Handle state effect using smart views
hStateSmart
    :: forall tag m sig sigs sigl l s a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => SmartProg (Sig (StateF tag s :+: sig) sigs sigl l) a
    -> (s -> m (s, a))
hStateSmart = unSTC . smartFold point con
{-# INLINE hStateSmart #-}

-- | Handle state effect with 'Codensity' representation
runStateC
    :: forall tag m sig sigs sigl s l a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => s
    -> Cod (STC tag s m) a
    -> m (s, a)
runStateC s p = unSTC (runCod var p) s
{-# INLINE runStateC #-}

{- | Run a state computation with codensity transformation

This is a version of 'runState' that omits the final state.
-}
runStateC'
    :: forall tag m sig sigs sigl s l a
     . (EffectMonad m sig sigs sigl (StateL s l))
    => s
    -> Cod (STC tag s m) a
    -> m a
runStateC' s p = snd <$> unSTC (runCod var p) s
{-# INLINE runStateC' #-}

instance StateCarrier (STC tag s) s
instance Forward 'State (STC tag s) (StateL s)
instance LCarrier (StateL s) ((,) s) where
    concatM (_, x) = x

-- | Algebra for handling state effect
algS :: StateF tag s (s -> m a) -> s -> m a
algS (Get k) s = k s s
algS (Modify f k) s = k (f s)

-- | 'TermAlgebra' instance for handling state effect
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

{- | State carrier newtype

Combines other carrier types with @s -> (s, a)@.
-}
newtype STC tag s m a = STC {unSTC :: s -> m (s, a)}
    deriving (Functor)

instance (Pointed m) => Pointed (STC tag s m) where
    point x = STC (\s -> point (s, x))
    {-# INLINE point #-}

{- | State latent carrier

Combines @(s,)@ with a latent carrier @l@.
-}
newtype StateL s l a = StateL {unStateL :: (s, l a)}
    deriving (Functor, Show)

{- | Class for identifying state tags

Provides a string identifier for debugging and tracing purposes.
-}
class Identify a where
    identify :: String

--- Renaming ---

{- | Rename effect tag

Used to identify renaming-related state operations
-}
data Rename

instance Identify Rename where
    identify = "Rename"

{- | Renaming state

Contains the current renaming, supply of fresh references, and the
'QName' of the current function scope (used for providing source code
locations with references).
-}
data RState = RState {renaming :: [(VarIndex, Ptr)], supply :: !UniqSupply, currentQName :: Maybe QName}

-- | Initialize a new RState with the given unique supply and an empty renaming
initRenaming :: UniqSupply -> RState
initRenaming sup = RState [] sup Nothing

{- | Renaming effect type

Type alias for StateF with Rename tag and RState
-}
type Renaming = StateF Rename RState

instance Show RState where
    show _ = "RState"

{- | Generate @n@ fresh names

Generates unique references using the renaming supply and updates the state
-}
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

{- | Create a new renaming scope

Resets the renaming table and sets the current function's 'QName'.
-}
newRenamingScope :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => QName -> m ()
newRenamingScope qn =
    logCall >> modify @Rename (\r -> r{renaming = [], currentQName = Just qn})
{-# INLINE newRenamingScope #-}

-- | Get the qualified name of the current function scope
getCurrentQName :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => m (Maybe QName)
getCurrentQName = logCall >> fmap currentQName (get @Rename)
{-# INLINE getCurrentQName #-}

{- | Lookup a variable index in the renaming table

Looks @v@ up in the current renaming table and returns the corresponding 'Ptr'.
Produces an error if the variable index is not found.
-}
lookupRenaming :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => VarIndex -> m Ptr
lookupRenaming v =
    logCall >> do
        r <- get @Rename
        case lookup v (renaming r) of
            Just !v' -> return v'
            Nothing -> error $ "lookupRenaming: " ++ show v ++ " in "
{-# INLINE lookupRenaming #-}

{- | Rename a list of variable indices

Generates fresh pointers for each element of @vs@ and updates the renaming
to map old indices to new pointers.
-}
rename :: (EffectCons m sig sigs sigl l, Renaming :<: sig) => [VarIndex] -> m [Ptr]
rename vs =
    logCall >> do
        r <- get @Rename
        let (vs', sup') = renameFromSupply (currentQName r) vs (supply r)
        put @Rename (r{renaming = renaming r ++ zip vs vs', supply = sup'})
        return vs'
{-# INLINE rename #-}

{- | Helper function for renaming a list of variable indices with an optional
function name
-}
renameFromSupply :: Maybe QName -> [VarIndex] -> UniqSupply -> ([Ptr], UniqSupply)
renameFromSupply _ [] sup = ([], sup)
renameFromSupply mqn (v : vs) sup =
    let (!u, sup') = takeUniqFromSupply sup
        !i = fromIntegral (getKey u)
        (is, sup'') = renameFromSupply mqn vs sup'
        loc = case mqn of
            Just (mdl, fn) -> mdl ++ "." ++ fn ++ " " ++ show v
            Nothing -> show v
    in  (mkPtr i loc : is, sup'')

--- Constraint store ---

{- | Equational constraint type

* 'VarC': Variable constraint
* 'ConsC': Constructor constraint
* 'LitC': Literal constraint
-}
data CValue
    = VarC Ptr
    | ConsC QName [Ptr]
    | LitC Literal
    deriving (Show, Eq)

{- | Constraints type

A map from pointers to constraint values.
-}
type Constraints = Map.Map Ptr CValue

{- | Lookup a 'Ptr' in the constraint store

Returns a constraint for a given pointer, if it exists.
-}
lookupC :: Ptr -> Constraints -> Maybe CValue
lookupC = Map.lookup
{-# INLINE lookupC #-}

-- | Add a constraint to the constraint map
addC :: Ptr -> CValue -> Constraints -> Constraints
addC = Map.insert
{-# INLINE addC #-}

{- | Constraint store effect tag

Used to identify constraint store-related state operations
-}
data CStore

instance Identify CStore where
    identify = "CStore"

{- | Constraint store effect type

Type alias for StateF with CStore tag and Constraints
-}
type ConstraintStore = StateF CStore Constraints

--- Tracing ---

{- | Trace information

* 'opName': The name of the operation
* 'details': Additional details about the operation (e.g. function name)
* 'primOp': Whether this is a primitive operation

An operation is primitive, if it has its own node constructor. If an operation
is a smart constructor that uses reuses other effect nodes, it is a non-
primitive operation.
-}
data TraceInfo = TI {opName :: String, details :: String, primOp :: Bool}
    deriving (Eq, Ord, Show)

{- | Pretty-print 'TraceInfo'

Formats the trace info, omitting details if empty
-}
prettyTI :: TraceInfo -> String
prettyTI (TI op dtls _)
    | dtls == "" = op
    | otherwise = op ++ " (" ++ dtls ++ ")"

{- | Trace effect tag

Used to identify trace-related state operations
-}
data Trace

instance Identify Trace where
    identify = "Trace"

{- | Tracing effect type

Type alias for StateF with Trace tag and list of TraceInfo
-}
type Tracing = StateF Trace [TraceInfo]

{- | Effect context constraint

Bundles TermMonad, Tracing effect, and HasCallStack constraints.
-}
type EffectCons m sig sigs sigl l = (TermMonad m (Sig sig sigs sigl l), Tracing :<: sig, HasCallStack)

{- | Log a primitive call for tracing

When tracing is active, records the calling function name as a primitive operation.
-}
logPrimCall :: (EffectCons m sig sigs sigl l) => m ()
logPrimCall
    | tracingActive = case getCallStack callStack of
        (_ : (name, _) : _) -> modifyWithoutLog (TI name "" True :)
        _ -> return ()
    | otherwise = return ()
  where
    modifyWithoutLog f = injectA (Modify @Trace f (return ()))
{-# INLINE logPrimCall #-}

{- | Log a non-primitive call for tracing

When tracing is active, records the calling function name as a non-primitive operation.
-}
logCall :: (EffectCons m sig sigs sigl l) => m ()
logCall
    | tracingActive = case getCallStack callStack of
        (_ : (name, _) : _) -> modifyWithoutLog (TI name "" False :)
        _ -> return ()
    | otherwise = return ()
  where
    modifyWithoutLog f = injectA (Modify @Trace f (return ()))
{-# INLINE logCall #-}

{- | Log a call with custom details for tracing

When tracing is active, records the calling function name with custom details.
-}
logCallWith :: (EffectCons m sig sigs sigl l) => String -> Bool -> m ()
logCallWith s prim
    | tracingActive = case getCallStack callStack of
        (_ : (name, _) : _) -> modifyWithoutLog (TI name s prim :)
        _ -> return ()
    | otherwise = return ()
  where
    modifyWithoutLog f = injectA (Modify @Trace f (return ()))
{-# INLINE logCallWith #-}

{- | Generate statistics from trace information

Returns a pair of lists: (primitive operations, combined operations),
each containing 'TraceInfo' paired with their execution counts, sorted by count.
-}
statistics :: [TraceInfo] -> ([(TraceInfo, Int)], [(TraceInfo, Int)])
statistics ti = (sortedCount prims, sortedCount comb)
  where
    (prims, comb) = partition primOp ti
    sortedCount = sortBy (\(_, n) (_, m) -> compare n m) . count
    count = Map.toList . Map.fromListWith (+) . map (,1)
{-# INLINE statistics #-}