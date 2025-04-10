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

import Data.Kind (Type)
import Effect.General.State (StateL (..), EffectCons, logCall)
import Signature
import Debug (ctrace, strace)
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.IntMap as IntMap
import Curry.FlatCurry (VarIndex)
import Data.Maybe (fromJust)
import Data.List (sortBy)
import System.Mem.StableName
import GHC.Weak
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.Primitive
import Type 
import System.Mem (performGC)
import GHC.Types.Unique.Supply
import GHC.Types.Unique (getKey)

data Thunking v :: Type -> (Type -> Type) -> Type where
   Thunk :: Ptr -> Thunking v () (OneSub v)
   Store :: Thunking v Ptr (OneSub v)
   Force :: Ptr -> Thunking v v NoSub
   Redirect :: (Ptr, Ptr) -> Thunking v () NoSub
   RunGC :: Thunking v () NoSub

store
   :: forall m sig sigs sigl v
    . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
   => m v
   -> m Ptr
store t = logCall >> let res = injectL (Store :: Thunking v Ptr (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
                     in case peek t of
                          Nothing -> res
                          Just sig -> case sig of
                             A (Algebraic op) -> res
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
thunk ptr t = logCall >> let res = injectL (Thunk ptr :: Thunking v () (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
                   in case peek t of
                          Nothing -> res
                          Just sig -> case sig of
                             A (Algebraic op) -> res
                             S (Enter _) -> res
                             L (Node op _ _ _) -> case prj3 op of
                              Just (Force ptr' :: Thunking v p c) -> redirect @v (ptr, ptr')
                              _ -> res
{-# INLINE thunk #-}

force :: (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => Ptr -> m v
force e = logCall >> injectL (Force e) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE force #-}

redirect :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => (Ptr, Ptr) -> m ()
redirect p = logCall >> injectL (Redirect p :: Thunking v () NoSub) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE redirect #-}

runGC :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => m ()
runGC = logCall >> injectL (RunGC :: Thunking v () NoSub) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE runGC #-}

runLazy :: (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m) => UniqSupply -> Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazy sup = fmap (\(s, r) -> strace (showTS s) r) . \p -> hLazy p (TS sup IntMap.empty)
{-# INLINE runLazy #-}

runLazySmart :: (Functor l, Show (l v), Show (l ()), m ~ SmartProg (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m) => UniqSupply -> SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazySmart sup = fmap (\(s, r) -> strace (showTS s) r)  . \p -> hLazySmart p (TS sup IntMap.empty)
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
   con (L (Node (Inl3 (Thunk ptr)) l st k)) = MC $ \(TS sup th) -> ctrace ("thunked " ++ show ptr) $ do
    unMC (k l) (TS sup (addEntry ptr (Thunked (unsafeCoerce $ st One)) th))
   con (L (Node (Inl3 Store) l st k)) = MC $ \(TS sup th) -> ctrace ("stored ") $ 
     let (!fresh, sup') = freshPtr sup
         th' = if ptrKey fresh `mod` 20000 == 0 then purge th else th
     in unMC (k (fresh <$ l)) (TS sup' (addEntry fresh (Thunked (unsafeCoerce $ st One)) th'))
   con (L (Node (Inl3 (Force p)) l st k)) = MC $ \ts -> ctrace ("force") $ retrieve p ts
     where retrieve ptr ts@(TS _ th) = case lookupEntry ptr th of
             Thunked t -> do
                (TS sup' th', lv) <- unMC (unsafeCoerce $ t l) ts
                unMC (k lv) (ctrace ("evaluate " ++ show ptr ++ show lv) (TS sup' (addEntry ptr (Evaluated lv) th')))
             Evaluated lv -> ctrace ("memoized " ++ show ptr ++ show lv) $ unMC (k lv) ts
             Redirected p' -> ctrace ("redirect " ++ show ptr ++ " -> " ++ show p') $ retrieve p' ts
   con (L (Node (Inl3 (Redirect (p, p'))) l _ k)) = MC $ \(TS sup th) -> ctrace ("redirect " ++ show (p,p')) $ do
    let skipRedirects th ptr = case lookupEntry ptr th of
             Redirected ptr' -> skipRedirects th ptr'
             _ -> ptr    
    unMC (k l) (TS sup (addEntry p (Redirected (skipRedirects th p')) th))
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



runLazyC :: (EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Functor l, Show (l v)) => UniqSupply -> Cod (MC m l v) a -> m a
runLazyC sup p = (\(s, r) -> ctrace (showTS s) r) <$> unMC (runCod var p) (TS sup IntMap.empty)
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

data ThunkStore l v = forall m. TS UniqSupply (TSM m l v) --(IntMap.IntMap (Entry m l v))
type TSM m l v = IntMap.IntMap (Weak (Entry m l v))

addEntry :: Ptr -> Entry m l v -> TSM m l v -> TSM m l v
addEntry (Ptr !i) p th = IntMap.insert i w th
  where w = unsafePerformIO $ mkWeak i (unsafeCoerce p) Nothing
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

purge :: Show (l v) => TSM m l v -> TSM m l v
purge m = strace stats m'
-- purge m = strace stats m'
  where
    m' = IntMap.filter isAlive m
    old = IntMap.size m
    new = IntMap.size m'
    stats = if old == 0 then "" else "Purged " ++ show (old - new) ++ " dead pointers of total " ++ show old ++ " pointers (now " ++ show new ++ ")" -- ++ showTS (TS undefined m')
    isAlive w = case unsafePerformIO $ deRefWeak w of
                 Just _ -> True
                 Nothing -> False
{-# NOINLINE purge #-}

majorPurge :: Show (l v) => TSM m l v -> TSM m l v
majorPurge m | IntMap.size m == IntMap.size m' = m'
             | otherwise = majorPurge m'
   where m' = unsafePerformIO $ performGC >> return (purge m)
{-# NOINLINE majorPurge #-}

newtype MC m l v a = MC {unMC :: ThunkStore l v -> m (ThunkStore l v, a)}

instance (Functor m) => Functor (MC m l v) where
   fmap f (MC x) = MC $ \th -> fmap (fmap f) (x th)
   {-# INLINE fmap #-}

instance Show (StableName a) where
   show sn = show (hashStableName sn)

showTS :: (Show (l v)) => ThunkStore l v -> String
showTS (TS i im) = let m = IntMap.mapMaybe (\w -> unsafePerformIO $ deRefWeak w) (majorPurge im) 
  in "MAJOR PURGE!\n" 
  ++ concat (sortBy cmp ((map ((++ "\n") . show . (\(i, (Evaluated lv)) -> (i, lv))) ((filter (\(_, (e)) -> isEvaluated e)) (IntMap.toList m)))
  ++ (map ((++ "\n") . show . (\(i, (Thunked lv)) -> (i, ("-")))) ((filter (\(_, (e)) -> isThunked e)) (IntMap.toList m)))
  ++ (map ((++ "\n") . show . (\(i, (Redirected p)) -> (i, ("-> " ++ show p)))) ((filter (\(_, (e)) -> isRedirected e)) (IntMap.toList m)))))

  ++ "unpurged: " ++ show (IntMap.size im) ++ " purged: " ++ show (IntMap.size m) ++ "\n\n"
  ++ "evaluated: " ++ show (length (filter (\(e) -> isEvaluated e) $ map snd (IntMap.toList m)))
  ++ " thunks: " ++ show (length ((filter (\(e) -> isThunked e)) $ map snd (IntMap.toList m)))
  ++ " redirects: " ++ show (length ((filter (\(e) -> isRedirected e)) $ map snd (IntMap.toList m)))
    where cmp ('(':s1) ('(':s2) = compare (read (takeInt s1) :: Int) (read (takeInt s2) :: Int)
          takeInt = takeWhile (/= ',')
{-# NOINLINE showTS #-}

instance (Show (l v)) => Show (ThunkStore l v) where
   show = showTS
