{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE FlexibleContexts #-}
{-# HLINT ignore "Use >=>" #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{- | Memoization effect

This module provides an effect for implementing lazy evaluation.
Furthermore, it contains a garbage collector for the internal
heap representation und provides the capability to inspect the
internal heap.
-}
module Effect.General.Memoization (
    Thunking,
    force,
    store,
    redirect,
    thunk,
    ThunkStore,
    MC,
    runLazy,
    runLazySmart,
    runLazyC,
    eval,
    dumpMemory,
    retrieve,
) where

import Free

import Control.Monad.Primitive
import qualified Data.IntMap.Strict as IntMap
import Data.Kind (Type)
import Data.List (sortBy)
import Data.Maybe (fromJust, isJust)
import Debug (strace)
import Effect.General.State (EffectCons, StateL (..), logPrimCall)
import Forwarding
import GHC.Types.Unique.Supply
import GHC.Weak
import Signature
import System.IO.Unsafe (unsafePerformIO)
import Type
import Unsafe.Coerce (unsafeCoerce)

{- | Memoization effect operations

* 'Thunk': Create a thunk for a specific pointer
* 'Store': Create a thunk (with location info) generating a new pointer
* 'Eval': Evaluate *without* memoizing the result
* 'Force': Evaluate a the computation associated with a pointer
* 'Redirect': Redirect one pointer to another
* 'DumpMemory': Dump heap contents
-}
data Thunking v :: Type -> (Type -> Type) -> Type where
    Thunk :: Ptr -> Thunking v () (OneSub v)
    Store :: String -> Thunking v Ptr (OneSub v)
    Eval :: Thunking v () (OneSub v)
    Force :: Bool -> Ptr -> Thunking v v NoSub
    Redirect :: (Ptr, Ptr) -> Thunking v () NoSub
    DumpMemory :: Thunking v () NoSub

{- | Store a computation in a new thunk

Creates a new thunk, stores the computation, and returns the pointer
-}
store
    :: forall m sig sigs sigl v
     . (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl)
    => String
    -> m v
    -> m Ptr
store loc t =
    let res = logPrimCall >> injectL (Store loc) (Id ()) (\One _ -> fmap Id t) (return . unId)
    in  inspect t res return
{-# INLINE store #-}

{- | Create a thunk at a specific pointer

Creates the thunk and sets up redirection if needed
-}
thunk
    :: forall m sig sigs sigl v
     . (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl)
    => Ptr
    -> m v
    -> m ()
thunk ptr t =
    let res = logPrimCall >> injectL (Thunk ptr) (Id ()) (\One _ -> fmap Id t) ((return . unId) :: Id () -> m ())
    in  inspect t res (\ptr' -> redirect @v (ptr, ptr'))
{-# INLINE thunk #-}

{- | Inspect a computation to avoid duplicate work

Checks if the computation is already being evaluated to avoid infinite loops
-}
inspect
    :: forall m sig sigs sigl v a
     . (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl)
    => m v -> m a -> (Ptr -> m a) -> m a
inspect p new recycle = case peek p of
    Nothing -> new
    Just sig -> case sig of
        A (Algebraic _) -> new
        S (Enter _) -> new
        L (Node op _ _ _) -> case prj3 op of
            Just (Force _ ptr' :: Thunking v p c) -> recycle ptr'
            _ -> new
{-# INLINE inspect #-}

{- | Force evaluation of a thunk

Evaluates the thunk at the given pointer and returns the result
-}
force :: (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl) => Ptr -> m v
force e = logPrimCall >> injectL (Force False e) (Id ()) absurdNoSub (return . unId)
{-# INLINE force #-}

{- | Retrieve the value from a thunk

Evaluates the thunk at the given pointer and marks it for deletion
-}
retrieve :: (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl) => Ptr -> m v
retrieve e = logPrimCall >> injectL (Force True e) (Id ()) absurdNoSub (return . unId)
{-# INLINE retrieve #-}

{- | Redirect one pointer to another

Sets up a redirection so that accessing one pointer returns the value from another
-}
redirect :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl) => (Ptr, Ptr) -> m ()
redirect p = logPrimCall >> injectL (Redirect p :: Thunking v () NoSub) (Id ()) absurdNoSub (return . unId)
{-# INLINE redirect #-}

{- | Dump memory statistics for debugging

Dumps the current state of the thunk store.
-}
dumpMemory
    :: forall v m sig sigs sigl
     . (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl)
    => m ()
dumpMemory = logPrimCall >> injectL (DumpMemory :: Thunking v () NoSub) (Id ()) absurdNoSub (return . unId)

{- | Evaluate a computation *without* memoization

Used for implementing 'bindIO', where side-effects should not be memoized.
-}
eval
    :: forall m sig sigs sigl v
     . (EffectCons m sig sigs sigl Id, Thunking v :<<: sigl)
    => m v
    -> m ()
eval t =
    logPrimCall
        >> injectL (Eval :: Thunking v () (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
{-# INLINE eval #-}

{- | Handle memoization effect with tree-based representation

Requires a 'UniqSupply' for generating fresh references.
-}
runLazy :: (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l)) => UniqSupply -> Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazy sup = fmap (\(s, r) -> strace (showTS s) r) . \p -> hLazy p (TS sup IntMap.empty)
{-# INLINE runLazy #-}

-- | Handle memoization effect with tree-based representation
hLazy
    :: forall m sig sigs sigl l v a
     . (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l))
    => Prog (Sig sig sigs (Thunking v :+++: sigl) l) a
    -> ThunkStore l v
    -> m (ThunkStore l v, a)
hLazy = unMC . fold point con
{-# INLINE hLazy #-}

{- | Handle memoization effect using smart views

Requires a 'UniqSupply' for generating fresh references.
-}
runLazySmart :: (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l)) => UniqSupply -> SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazySmart sup = fmap (\(s, r) -> strace (showTS s) r) . \p -> hLazySmart p (TS sup IntMap.empty)
{-# INLINE runLazySmart #-}

-- | Handle memoization effect using smart views
hLazySmart
    :: forall m sig sigs sigl l v a
     . (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l))
    => SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) a
    -> ThunkStore l v
    -> m (ThunkStore l v, a)
hLazySmart = unMC . smartFold point con
{-# INLINE hLazySmart #-}

{- | Handle memoization effect with 'Codensity' representation

Requires a 'UniqSupply' for generating fresh references.
-}
runLazyC :: (EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Functor l, Show (l v)) => UniqSupply -> Cod (MC l v m) a -> m a
runLazyC sup p = (\(s, r) -> strace (showTS s) r) <$> unMC (runCod var p) (TS sup IntMap.empty)
{-# INLINE runLazyC #-}

instance StateCarrier (MC l v) (ThunkStore l v)
instance Forward 'State (MC l v) (StateL (ThunkStore l v))

-- | Algebra for handling memoization effect
algLazy
    :: (Monad m, Functor l, Show (l v))
    => Latent (Thunking v) l (MC l v m) (MC l v m a)
    -> MC l v m a
algLazy (Node op l st' k') = MC $ \ts@(TS sup th) ->
    let k = unMC . k'
        st c' l' = unMC $ st' c' l'
    in  case op of
            Thunk ptr -> k l (TS sup (addEntry ptr (Thunked (MC . st One)) th))
            Store loc ->
                let (!fresh, sup') = freshPtr sup loc
                    th' = if ptrKey fresh `mod` 20000 == 0 then purge th else th
                in  k (fresh <$ l) (TS sup' (addEntry fresh (Thunked (MC . st One)) th'))
            Eval -> st One l ts >> k l ts
            Force delete p -> fetch p
              where
                fetch ptr = case lookupEntry ptr th of
                    Thunked t -> do
                        (TS sup' th', lv) <- unMC (t l) (if delete then TS sup (removeEntry ptr th) else ts)
                        let th'' = if delete then removeEntry ptr th' else addEntry ptr (Evaluated lv) th'
                        k lv (TS sup' th'')
                    Evaluated lv ->
                        let th' = if delete then removeEntry ptr th else th
                        in  k lv (TS sup th')
                    Redirected p' -> fetch p'
            Redirect (p, p') -> do
                let skipRedirects th' ptr = case lookupEntry ptr th' of
                        Redirected ptr' -> skipRedirects th' ptr'
                        _ -> ptr
                k l (TS sup (addEntry p (Redirected (skipRedirects th p')) th))
            DumpMemory -> unsafePerformIO (putStrLn (showTS ts)) `seq` k l ts

-- | 'TermAlgebra' instance for handling thunking effect
instance (Functor l, EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Show (l v)) => TermAlgebra (MC l v m) (Sig sig sigs (Thunking v :+++: sigl) l) where
    con (A op) = afwd op
    con (S op) = sfwd op
    con (L (Node op l st k)) = case op of
        (Inl3 op') -> algLazy (Node op' l st k)
        (Inr3 op') -> lfwd @_ @'State (Node op' l st k)
    {-# INLINE con #-}
    var = MC . (\x th -> point (th, x))
    {-# INLINE var #-}

instance (Pointed m) => Pointed (MC l v m) where
    point x = MC $ \th -> point (th, x)
    {-# INLINE point #-}

{- | Entry type for thunk store

* 'Thunked': A computation that hasn't been evaluated yet
* 'Evaluated': A computation that has been evaluated to a value
* 'Redirected': A pointer that redirects to another pointer
-}
data Entry m l v = Thunked (l () -> MC l v m (l v)) | Evaluated (l v) | Redirected Ptr

-- | Check if an entry is a thunk
isThunked :: Entry m l v -> Bool
isThunked (Thunked _) = True
isThunked _ = False

-- | Check if an entry is a value
isEvaluated :: Entry m l v -> Bool
isEvaluated (Evaluated _) = True
isEvaluated _ = False

-- | Check if an entry is a redirect
isRedirected :: Entry m l v -> Bool
isRedirected (Redirected _) = True
isRedirected _ = False

{- | Thunk store for memoization

Stores thunks and their evaluation states using weak pointers for garbage collection.

The existential quantification for @m@ is required, as exposing @m@ in 'ThunkStore' would
prevent instance resolution for 'TermAlgebra' from termination. Without 'TermAlgebra'
infrastructure this is not a problem, as the recursion is encapsulated within data types.
-}
data ThunkStore l v = forall m. TS !UniqSupply !(TSM m l v)

{- | Thunk store map type

Maps pointer keys to entries with weak pointers for garbage collection.
-}
type TSM m l v = IntMap.IntMap (String, Weak (Entry m l v))

{- | Add an entry to the thunk store

Creates a weak pointer for the entry and adds it to the map.
-}
addEntry :: Ptr -> Entry m' l v -> TSM m l v -> TSM m l v
addEntry (Ptr !i loc) p th = unsafePerformIO $ do
    w <- mkWeak i (unsafeCoerce p) Nothing
    return (IntMap.insert i (loc, w) th)
{-# NOINLINE addEntry #-}

{- | Remove an entry from the thunk store

Deletes the entry with the given pointer.
-}
removeEntry :: Ptr -> TSM m l v -> TSM m l v
removeEntry (Ptr !i _) = IntMap.delete i
{-# INLINE removeEntry #-}

{- | Lookup an entry in the thunk store

Retrieves the entry for a given pointer, following weak pointers.
Produces an error if the weak pointer is dead or the pointer is not found.
-}
lookupEntry :: Ptr -> TSM m l v -> Entry m' l v
lookupEntry (Ptr !i _) th = unsafePerformIO $ keepAlive i $ do
    case IntMap.lookup i th of
        Just (_, w) -> do
            m <- deRefWeak w
            case m of
                Just v -> return (unsafeCoerce v)
                Nothing -> error ("Weak pointer " ++ show i ++ " is dead!")
        Nothing -> error $ "VarIndex not found: " ++ show i
{-# NOINLINE lookupEntry #-}

{- | Purge dead pointers from the thunk store map

Filters out entries with dead weak pointers and logs statistics.
-}
purge :: TSM m l v -> TSM m l v
purge m = strace stats m'
  where
    m' = IntMap.filter isAlive m
    old = IntMap.size m
    new = IntMap.size m'
    stats = if old == 0 then "empty" else "Purged " ++ show (old - new) ++ " dead pointers of total " ++ show old ++ " pointers (now " ++ show new ++ ")" -- ++ showTS (TS undefined m')
    isAlive (_, w) = case unsafePerformIO $ deRefWeak w of
        Just _ -> True
        Nothing -> False
{-# NOINLINE purge #-}

{- | Thunking carrier newtype

Combines other carrier types with the state carrier specialized to 'ThunkStore'.
-}
newtype MC l v m a = MC {unMC :: ThunkStore l v -> m (ThunkStore l v, a)}

instance (Functor m) => Functor (MC l v m) where
    fmap f (MC x) = MC $ \th -> fmap (fmap f) (x th)
    {-# INLINE fmap #-}

{- | Show a thunk store as a string for debugging purposes

Displays memory statistics including alive/dead pointers and evaluation states.
-}
showTS :: (Show (l v)) => ThunkStore l v -> String
showTS (TS _ im) =
    let m = IntMap.map deRefPair im
        deRefPair (s, w) = (s,) <$> (unsafePerformIO . deRefWeak) w
        (alive, dead) = IntMap.partition isJust m
        xs = IntMap.toList (IntMap.map fromJust alive)
        evls = filter (isEvaluated . snd . snd) xs
        thnks = filter (isThunked . snd . snd) xs
        rdrs = filter (isRedirected . snd . snd) xs
    in  concat
            ( sortBy
                cmp
                (map prettyVal xs)
            )
            ++ "alive: "
            ++ show (IntMap.size alive)
            ++ " dead: "
            ++ show (IntMap.size dead)
            ++ "\n"
            ++ "evaluated: "
            ++ show (length evls)
            ++ " thunks: "
            ++ show (length thnks)
            ++ " redirects: "
            ++ show (length rdrs)
            ++ "\n\n"
  where
    cmp s1 s2 = compare (read (takeInt s1) :: Int) (read (takeInt s2) :: Int)
    takeInt = takeWhile (/= '(')
{-# NOINLINE showTS #-}

{- | Pretty-print a thunk store entry

Formats an entry with its pointer, location, and evaluation state.
-}
prettyVal :: (Show (l v)) => (Int, (String, Entry m l v)) -> String
prettyVal (i, (loc, e)) =
    show i
        ++ " ("
        ++ loc
        ++ ")"
        ++ ( case e of
                Evaluated lv -> " = (" ++ show lv ++ ")"
                Thunked _ -> ""
                Redirected (Ptr ptr _) -> " -> " ++ show ptr
           )
        ++ "\n"

instance (Show (l v)) => Show (ThunkStore l v) where
    show = showTS
