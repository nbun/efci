{-# LANGUAGE AllowAmbiguousTypes #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# HLINT ignore "Use >=>" #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE BangPatterns #-}

module Effect.General.Memoization where

import Free

import Data.Bifunctor (second)
import Data.Either (rights, lefts, isRight, isLeft, fromRight)
import Data.Kind (Type)
import Effect.General.State (StateL (..), EffectCons, logCall, StateF (..), Renaming, Identify (..), modify, get, put)
import Signature
import Debug (ctrace, strace)
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace (trace)
import Data.Union (prj)
import qualified Data.IntMap as IntMap
import Data.IntMap ((!))
import Curry.FlatCurry (VarIndex)
import Data.Maybe (fromJust, mapMaybe)
import Data.List (nub)
import Control.Monad (join)
import qualified Data.HashMap.Strict as HashMap
import System.Mem.StableName
import GHC.Weak
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.Primitive
import Type (analyzeVarIndex)

data Thunking v :: Type -> (Type -> Type) -> Type where
   Thunk :: Ptr -> Thunking v () (OneSub v)
   Store :: Thunking v Ptr (OneSub v)
   Force :: Ptr -> Thunking v v NoSub
   Redirect :: [(Ptr, Ptr)] -> Thunking v () NoSub
   RunGC :: Thunking v () NoSub

store
   :: forall m sig sigs sigl v
    . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
   => m v
   -> m Ptr
store t = logCall >> injectL (Store :: Thunking v Ptr (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
{-# INLINE store #-}

thunk
   :: forall m sig sigs sigl v
    . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
   => Ptr
   -> m v
   -> m ()
thunk ptr t = logCall >> (injectL (Thunk ptr :: Thunking v () (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId))
{-# INLINE thunk #-}

force :: (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => Ptr -> m v
force e = logCall >> injectL (Force e) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE force #-}

redirect :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => [(Ptr, Ptr)] -> m ()
redirect ps = logCall >> injectL (Redirect ps :: Thunking v () NoSub) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE redirect #-}

type Ptr = Int

runGC :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => m ()
runGC = logCall >> injectL (RunGC :: Thunking v () NoSub) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE runGC #-}

runLazy :: (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m) => Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazy = fmap snd . \p -> hLazy p (TS (2^31) HashMap.empty)
{-# INLINE runLazy #-}

runLazySmart :: (Functor l, Show (l v), Show (l ()), m ~ SmartProg (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m) => SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazySmart = fmap (\(s, r) -> strace (showTS s) r)  . \p -> hLazySmart p (TS (2^31) HashMap.empty)
{-# INLINE runLazySmart #-}

hLazy
   :: forall m n sig sigs sigl l v a
    . (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m)
   => Prog (Sig sig sigs (Thunking v :+++: sigl) l) a
   -> ThunkStore l v
   -> m (ThunkStore l v, a)
hLazy = unMC . fold point con
{-# INLINE hLazy #-}

hLazySmart
   :: forall m n sig sigs sigl l v a
    . (Functor l, Show (l v), Show (l ()), m ~ SmartProg (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m)
   => SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) a
   -> ThunkStore l v
   -> m (ThunkStore l v, a)
hLazySmart = unMC . smartFold point con
{-# INLINE hLazySmart #-}

instance (Functor l, EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Show (l v)) => TermAlgebra (MC m l v) (Sig sig sigs (Thunking v :+++: sigl) l) where
   con (A (Algebraic op)) = MC $ \th -> con $ A $ Algebraic $ fmap (\x -> unMC x th) op
   con (S (Enter op)) = MC $ \th -> con $ S $ Enter $ fmap (go th) op
     where
      go th hhx = do
         (th', hx) <- unMC hhx th
         return (unMC hx th')
   con (L (Node (Inl3 (Thunk ptr)) l st k)) = MC $ \(TS fresh im) -> ctrace ("thunked " ++ show ptr) $ unMC (k l) (TS fresh (addEntry ptr (Thunked (unsafeCoerce $ st One)) im))
   con (L (Node (Inl3 Store) l st k)) = MC $ \(TS fresh im) -> ctrace ("stored " ++ show fresh) $ unMC (k (fresh <$ l)) (TS (fresh - 1) (addEntry fresh (Thunked (unsafeCoerce $ st One)) im))
   con (L (Node (Inl3 (Force p)) l st k)) = MC $ \ts@(TS _ th) -> ctrace ("forcelookup " {- ++ show (HashMap.keys th)-}) $ case lookupEntry p th of
      Thunked t -> do
         (TS fresh' th', lv) <- unMC (unsafeCoerce $ t l) ts
         unMC (k lv) (ctrace ("evaluate " ++ show p ++ show lv) (TS fresh' (addEntry p (Evaluated lv) th')))
      Evaluated lv -> ctrace ("memoized " ++ show p ++ show lv) $ unMC (k lv) ts
      Redirected p' -> ctrace ("redirect " ++ show p ++ " -> " ++ show p') $ unMC (con $ L $ Node (Inl3 (Force p')) l st k) ts
   con (L (Node (Inl3 (Redirect ps)) l _ k)) = MC $ \ts@(TS fresh th) -> ctrace ("redirect " ++ show ps) $ unMC (k l) (TS fresh (foldr (\(p, p') th' -> addEntry p (Redirected p') th') th ps)) 
   con (L (Node (Inl3 (RunGC)) l _ k)) = MC $ \ts@(TS _ _) -> undefined
      -- let ptrs = mapMaybe (\v -> Map.lookup v rm) vs 
      -- in unMC (k l) (garbageCollector ptrs ts)
   con (L (Node (Inr3 op) l st k)) = MC $ \th ->
      con $
         L $
            Node
               op
               (StateL (th, l))
               (\c (StateL (th', lv)) -> StateL <$> unMC (st c lv) th')
               (\(StateL (th', lv)) -> unMC (k lv) th')
   {-# INLINE con #-}
   var = MC . gen'Memo
     where
      gen'Memo x th = return (th, x)
   {-# INLINE var #-}

runLazyC :: (EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Functor l, Show (l v)) => Cod (MC m l v) a -> m a
runLazyC p = (\(s, r) -> ctrace (showTS s) r) <$> unMC (runCod var p) (TS 0 HashMap.empty)
-- runLazyC th p = snd <$> unMC (runCod var p) th
{-# INLINE runLazyC #-}

instance (Monad m) => Pointed (MC m l v) where
   point x = MC $ \th -> return (th, x)
   {-# INLINE point #-}

data Entry m l v = Thunked (l () -> MC m l v (l v)) | Evaluated (l v) | Redirected Ptr

isThunked, isEvaluated, isRedirected :: Entry m l v -> Bool
isThunked (Thunked _) = True
isThunked _ = False
isEvaluated (Evaluated _) = True
isEvaluated _ = False
isRedirected (Redirected _) = True
isRedirected _ = False

-- type StableName = Maybe

-- makeStableName = return . Just

data ThunkStore l v = forall m. TS Int (TSM m l v) --(HashMap.HashMap (Entry m l v))
type TSM m l v = HashMap.HashMap (StableName VarIndex) (Weak (Entry m l v))

addEntry :: VarIndex -> Entry m l v -> TSM m l v -> TSM m l v
addEntry !i p th = unsafePerformIO $ do
  trace (analyzeVarIndex "memoadd" i) (return ())
  sn <- makeStableName i
--   putStrLn ("Add VarIndex " ++ show i ++ " with stable name hash " ++ show (hashStableName sn))
  w <- mkWeak i (unsafeCoerce p) Nothing
  return (HashMap.insert sn w th)

lookupEntry :: VarIndex -> TSM m l v -> Entry m l v
lookupEntry !i th = unsafePerformIO $ keepAlive i $ do
  trace (analyzeVarIndex "memolookup" i) (return ())
  sn <- makeStableName i
  case HashMap.lookup sn th of
    Just w -> do
      m <- deRefWeak w
      case m of
        Just v -> return (unsafeCoerce v)
        Nothing -> error ("Weak pointer " ++ show i ++ " is dead!")
    Nothing -> error ("VarIndex " ++ show i ++ " with stable hash " ++ show (hashStableName sn) ++ " not found in " ++ show (map hashStableName $ HashMap.keys th))

newtype MC m l v a = MC {unMC :: ThunkStore l v -> m (ThunkStore l v, a)}

instance (Functor m) => Functor (MC m l v) where
   fmap f (MC x) = MC $ \th -> fmap (fmap f) (x th)
   {-# INLINE fmap #-}

showTS :: (Show (l v)) => ThunkStore l v -> String
showTS = undefined
-- showTS (TS i m) = show i ++ " \n"
--   ++ concatMap ((++ "\n") . show . (\(i, (Evaluated lv)) -> (i, (lv)))) ((filter (\(_, (e)) -> isEvaluated e)) (HashMap.toList m))
--   ++ concatMap ((++ "\n") . show . (\(i, (Thunked lv)) -> (i, ("-")))) ((filter (\(_, (e)) -> isThunked e)) (HashMap.toList m))
--   ++ concatMap ((++ "\n") . show . (\(i, (Redirected lv)) -> (i, ("-")))) ((filter (\(_, (e)) -> isRedirected e)) (HashMap.toList m))
--   ++ "\n evaluated: " ++ show (length (filter (\(e) -> isEvaluated e) $ map snd (HashMap.toList m)))
--   ++ " thunks: " ++ show (length ((filter (\(e) -> isThunked e)) $ map snd (HashMap.toList m)))
--   ++ " redirects: " ++ show (length ((filter (\(e) -> isRedirected e)) $ map snd (HashMap.toList m)))
-- {-# INLINE showTS #-}

instance (Show (l v)) => Show (ThunkStore l v) where
   show = undefined

garbageCollector :: (Show (l v)) => [Ptr] -> ThunkStore l v -> ThunkStore l v
garbageCollector ptrs ts@(TS i im) = undefined --TS i (Map.filterWithKey (\k _ -> k `elem` allPtrs) im)
--   where
--    allPtrs = trace ("GC start: " ++ show ptrs ++ "\n" ++ showTS ts ) go (nub ptrs)
--    go ps | length ps == length ps' = trace ("GC done: " ++ show ps') ps'
--          | otherwise = trace ("GC cont: " ++ show ps ++ " / " ++ show ps') go ps'
--       where ps' = nub (concatMap (pointsTo ts) ps ++ ps)