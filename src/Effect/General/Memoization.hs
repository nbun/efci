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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

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
    eval2HNF,
    dumpMemory,
) where

import Free

import Control.Monad.Primitive
import qualified Data.IntMap.Strict as IntMap
import Data.Kind (Type)
import Data.List (sortBy)
import Debug (ctrace, strace)
import Debug.HTrace (htrace)
import Effect.General.State (EffectCons, StateL (..), logCall)
import GHC.Types.Unique.Supply
import GHC.Weak
import Signature
import System.IO.Unsafe (unsafePerformIO)
import System.Mem (performGC)
import Type
import Unsafe.Coerce (unsafeCoerce)

data Thunking v :: Type -> (Type -> Type) -> Type where
    Thunk :: Ptr -> Thunking v () (OneSub v)
    Store :: Thunking v Ptr (OneSub v)
    Eval :: Thunking v () (OneSub v)
    Force :: Ptr -> Thunking v v NoSub
    Redirect :: (Ptr, Ptr) -> Thunking v () NoSub
    DumpMemory :: Thunking v () NoSub

dumpMemory
    :: forall v m sig sigs sigl
     . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
    => m ()
dumpMemory = logCall >> injectL (DumpMemory :: Thunking v () NoSub) (Id ()) absurdNoSub (return . unId)

eval2HNF
    :: forall m sig sigs sigl v
     . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
    => m v
    -> m ()
eval2HNF t =
    logCall
        >> injectL (Eval :: Thunking v () (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
{-# INLINE eval2HNF #-}

store
    :: forall m sig sigs sigl v
     . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
    => m v
    -> m Ptr
store t =
    logCall
        >> let res = injectL (Store :: Thunking v Ptr (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
            in case peek t of
                Nothing -> res
                Just sig -> case sig of
                    A (Algebraic _) -> res
                    S (Enter _) -> res
                    L (Node op _ _ _) -> case prj3 op of
                        Just (Force ptr' :: Thunking v p c) -> return ptr'
                        _ -> res
{-# INLINE store #-}

thunk
    :: forall m sig sigs sigl v
     . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
    => Ptr
    -> m v
    -> m ()
thunk ptr t =
    logCall
        >> let res = injectL (Thunk ptr :: Thunking v () (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
            in case peek t of
                Nothing -> res
                Just sig -> case sig of
                    A (Algebraic _) -> res
                    S (Enter _) -> res
                    L (Node op _ _ _) -> case prj3 op of
                        Just (Force ptr' :: Thunking v p c) -> redirect @v (ptr, ptr')
                        _ -> res
{-# INLINE thunk #-}

force :: (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => Ptr -> m v
force e = logCall >> injectL (Force e) (Id ()) absurdNoSub (return . unId)
{-# INLINE force #-}

redirect :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => (Ptr, Ptr) -> m ()
redirect p = logCall >> injectL (Redirect p :: Thunking v () NoSub) (Id ()) absurdNoSub (return . unId)
{-# INLINE redirect #-}

runLazy :: (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l)) => UniqSupply -> Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazy sup = fmap (\(s, r) -> strace (showTS s) r) . \p -> hLazy p (TS sup IntMap.empty)
{-# INLINE runLazy #-}

runLazySmart :: (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l)) => UniqSupply -> SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazySmart sup = fmap (\(s, r) -> strace (showTS s) r) . \p -> hLazySmart p (TS sup IntMap.empty)
{-# INLINE runLazySmart #-}

hLazy
    :: forall m sig sigs sigl l v a
     . (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l))
    => Prog (Sig sig sigs (Thunking v :+++: sigl) l) a
    -> ThunkStore l v
    -> m (ThunkStore l v, a)
hLazy = unMC . fold point con
{-# INLINE hLazy #-}

hLazySmart
    :: forall m sig sigs sigl l v a
     . (Functor l, Show (l v), Show (l ()), EffectCons m sig sigs sigl (StateL (ThunkStore l v) l))
    => SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) a
    -> ThunkStore l v
    -> m (ThunkStore l v, a)
hLazySmart = unMC . smartFold point con
{-# INLINE hLazySmart #-}

instance StateCarrier (MC l v) (ThunkStore l v)
instance DeriveForward 'State (MC l v) (StateL (ThunkStore l v))

algLazy
    :: (Monad m, Functor l, Show (l v))
    => Latent (Thunking v) l (MC l v m) (MC l v m a)
    -> MC l v m a
algLazy (Node op l st' k') = MC $ \ts@(TS sup th) ->
    let k = unMC . k'
        st c' l' = unMC $ st' c' l'
     in case op of
            Thunk ptr -> k l (TS sup (addEntry ptr (Thunked (unsafeCoerce $ st One)) th))
            Store ->
                let (!fresh, sup') = freshPtr sup
                    th' = if ptrKey fresh `mod` 20000 == 0 then purge th else th
                 in k (fresh <$ l) (TS sup' (addEntry fresh (Thunked (unsafeCoerce $ st One)) th'))
            Eval -> st One l ts >> k l ts
            Force p -> retrieve p
              where
                retrieve ptr = case lookupEntry ptr th of
                    Thunked t -> do
                        (TS sup' th', lv) <- unMC (unsafeCoerce $ t l) ts
                        k lv (TS sup' (addEntry ptr (Evaluated lv) th'))
                    Evaluated lv -> k lv ts
                    Redirected p' -> retrieve p'
            Redirect (p, p') -> do
                let skipRedirects th' ptr = case lookupEntry ptr th' of
                        Redirected ptr' -> skipRedirects th' ptr'
                        _ -> ptr
                k l (TS sup (addEntry p (Redirected (skipRedirects th p')) th))
            DumpMemory -> htrace (showTS ts) $ k l ts

instance (Functor l, EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Show (l v)) => TermAlgebra (MC l v m) (Sig sig sigs (Thunking v :+++: sigl) l) where
    con (A op) = afwd op
    con (S op) = sfwd op
    con (L (Node op l st k)) = case op of
        (Inl3 op') -> algLazy (Node op' l st k)
        (Inr3 op') -> lfwd @_ @'State (Node op' l st k)
    {-# INLINE con #-}
    var = MC . (\x th -> point (th, x))
    {-# INLINE var #-}

runLazyC :: (EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Functor l, Show (l v)) => UniqSupply -> Cod (MC l v m) a -> m a
runLazyC sup p = (\(s, r) -> ctrace (showTS s) r) <$> unMC (runCod var p) (TS sup IntMap.empty)
-- runLazyC th p = snd <$> unMC (runCod var p) th
{-# INLINE runLazyC #-}

instance (Pointed m) => Pointed (MC l v m) where
    point x = MC $ \th -> point (th, x)
    {-# INLINE point #-}

data Entry m l v = Thunked (l () -> MC l v m (l v)) | Evaluated (l v) | Redirected Ptr

isThunked, isEvaluated, isRedirected :: Entry m l v -> Bool
isThunked (Thunked _) = True
isThunked _ = False
isEvaluated (Evaluated _) = True
isEvaluated _ = False
isRedirected (Redirected _) = True
isRedirected _ = False

data ThunkStore l v = forall m. TS !UniqSupply !(TSM m l v) -- (IntMap.IntMap (Entry m l v))
type TSM m l v = IntMap.IntMap (Weak (Entry m l v))

addEntry :: Ptr -> Entry m l v -> TSM m l v -> TSM m l v
addEntry (Ptr !i) p th = unsafePerformIO $ do
    w <- mkWeak i (unsafeCoerce p) Nothing
    return (IntMap.insert i w th)
{-# NOINLINE addEntry #-}

lookupEntry :: Ptr -> TSM m l v -> Entry m l v
lookupEntry (Ptr !i) th = unsafePerformIO $ keepAlive i $ do
    case IntMap.lookup i th of
        Just w -> do
            m <- deRefWeak w
            case m of
                Just v -> return (unsafeCoerce v)
                Nothing -> error ("Weak pointer " ++ show i ++ " is dead!")
        Nothing -> error $ analyzeVarIndex "VarIndex not found: " i
{-# NOINLINE lookupEntry #-}

purge :: TSM m l v -> TSM m l v
purge m = strace stats m'
  where
    -- purge m = strace stats m'

    m' = IntMap.filter isAlive m
    old = IntMap.size m
    new = IntMap.size m'
    stats = if old == 0 then "empty" else "Purged " ++ show (old - new) ++ " dead pointers of total " ++ show old ++ " pointers (now " ++ show new ++ ")" -- ++ showTS (TS undefined m')
    isAlive w = case unsafePerformIO $ deRefWeak w of
        Just _ -> True
        Nothing -> False
{-# NOINLINE purge #-}

majorPurge :: (Show (l v)) => TSM m l v -> TSM m l v
majorPurge m
    | IntMap.size m == IntMap.size m' = m'
    | otherwise = majorPurge m'
  where
    m' = unsafePerformIO $ performGC >> return (purge m)
{-# NOINLINE majorPurge #-}

newtype MC l v m a = MC {unMC :: ThunkStore l v -> m (ThunkStore l v, a)}

instance (Functor m) => Functor (MC l v m) where
    fmap f (MC x) = MC $ \th -> fmap (fmap f) (x th)
    {-# INLINE fmap #-}

showTS :: (Show (l v)) => ThunkStore l v -> String
showTS (TS _ im) =
    let m = IntMap.mapMaybe (unsafePerformIO . deRefWeak) (majorPurge im)
        xs = IntMap.toList m
        evls = filter (isEvaluated . snd) xs
        thnks = filter (isThunked . snd) xs
        rdrs = filter (isRedirected . snd) xs
     in concat
            ( sortBy
                cmp
                ( map ((++ "\n") . show . (\(i, Evaluated lv) -> (i, lv))) evls
                    ++ map ((++ "\n") . show . (\(i, Thunked _) -> (i, "-"))) thnks
                    ++ map ((++ "\n") . show . (\(i, Redirected p) -> (i, "-> " ++ show p))) rdrs
                )
            )
            ++ "unpurged: "
            ++ show (IntMap.size im)
            ++ " purged: "
            ++ show (IntMap.size m)
            ++ "\n"
            ++ "evaluated: "
            ++ show (length evls)
            ++ " thunks: "
            ++ show (length thnks)
            ++ " redirects: "
            ++ show (length rdrs)
            ++ "\n\n"
  where
    cmp ('(' : s1) ('(' : s2) = compare (read (takeInt s1) :: Int) (read (takeInt s2) :: Int)
    takeInt = takeWhile (/= ',')
{-# NOINLINE showTS #-}

instance (Show (l v)) => Show (ThunkStore l v) where
    show = showTS
