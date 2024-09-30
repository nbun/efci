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

module Effect.General.Memoization where

import Free

import Data.Bifunctor (second)
import Data.Either (rights, lefts)
import Data.Kind (Type)
import Effect.General.State (StateL (..), EffectCons, logCall, StateF (..), Renaming, Identify (..), Scope, modify, get)
import Signature
import Debug (ctrace, strace)
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace (trace)
import Data.Union (prj)
import qualified Data.Map as Map
import Data.Map ((!))
import Curry.FlatCurry (VarIndex)

type ScpVarIndex = (Scope, VarIndex)
type Ptr' = VarIndex

data Thunking v :: Type -> (Type -> Type) -> Type where
   Thunk :: Thunking v Ptr' (OneSub v)
   Force :: Either Ptr' ScpVarIndex -> Thunking v v NoSub
   Add   :: [(ScpVarIndex, Ptr')] -> Thunking v () NoSub
   GetPtr :: ScpVarIndex -> Thunking v Ptr' NoSub

addBindings :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => [(ScpVarIndex, Ptr')] -> m ()
addBindings bs = logCall >> injectL (Add bs :: Thunking v () NoSub) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE addBindings #-}

getPtr :: forall v m sig sigs sigl. (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => ScpVarIndex -> m Ptr'
getPtr p = logCall >> injectL (GetPtr p :: Thunking v Ptr' NoSub) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE getPtr #-}

thunk
   :: forall m sig sigs sigl v
    . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
   => m v
   -> m Ptr'
thunk t = logCall >> let res = injectL (Thunk :: Thunking v Ptr' (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
                     in case peek t of
                          Nothing -> res
                          Just sig -> case sig of
                             A (Algebraic op) -> res
                             S (Enter _) -> res
                             L (Node op _ _ _) -> case prj3 op of
                              Just (Force e :: Thunking v p c) -> case e of
                                 Left i -> return i
                                 Right v -> getPtr @v v
                              _ -> res
{-# INLINE thunk #-}

force :: (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => Either Ptr' (VarIndex, Scope) -> m v
force e = logCall >> injectL (Force e) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE force #-}

type Ptr = Ptr'

runLazy :: (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m) => Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazy = fmap snd . \p -> hLazy p (TS 0 Map.empty Map.empty)
{-# INLINE runLazy #-}

runLazySmart :: (Functor l, Show (l v), Show (l ()), m ~ SmartProg (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m) => SmartProg (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazySmart = fmap (\(s, r) -> strace (showTS s) r)  . \p -> hLazySmart p (TS 0 Map.empty Map.empty)
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
   con (L (Node (Inl3 Thunk) l st k)) = MC $ \(TS fresh rm im) -> ctrace ("thunked " ++ show fresh) $ unMC (k ((fresh) <$ l)) (TS (fresh + 1) rm (Map.insert (fresh) (Left (unsafeCoerce $ st One))  im))
   con (L (Node (Inl3 (GetPtr i)) l _ k)) = MC $ \(TS fresh rm im) -> ctrace ("GetPtr " ++ show i) $ case Map.lookup i rm of
      Nothing -> undefined
      Just ptr -> unMC (k (ptr <$ l)) (TS fresh rm im)
   con (L (Node (Inl3 (Add bs)) l _ k)) = MC $ \(TS fresh rm im) -> ctrace ("Add " ++ show bs) $ unMC (k l) (TS fresh (Map.fromList bs `Map.union` rm) im)
   con (L (Node (Inl3 (Force e)) l _ k)) = MC $ \ts@(TS _ rm th) -> ctrace ("forcelookup " ++ show (Map.keys th)) $
      let ptr = case e of
           Left ptr -> ptr
           Right v -> case Map.lookup v rm of
                        Nothing -> error $ show rm ++ "\n\n" ++ show (Map.keys th) ++ "\n\n" ++ show e
                        Just ptr -> ptr
      in case Map.lookup ptr th of
         Nothing -> error $ show rm ++ "\n\n" ++ show (Map.keys th) ++ "\n\n" ++ show e
         Just e -> case e of
            Left t -> do
             (TS fresh' rm' th', lv) <- unMC (unsafeCoerce $ t l) ts
             unMC (k lv) (ctrace ("evaluate " ++ show ptr ++ show lv) (TS fresh' rm' (Map.insert ptr (Right lv) th')))
            Right lv -> ctrace ("memoized " ++ show ptr ++ show lv) $ unMC (k lv) ts
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
runLazyC p = (\(s, r) -> ctrace (showTS s) r) <$> unMC (runCod var p) (TS 0 Map.empty Map.empty)
-- runLazyC th p = snd <$> unMC (runCod var p) th
{-# INLINE runLazyC #-}

instance (Monad m) => Pointed (MC m l v) where
   point x = MC $ \th -> return (th, x)
   {-# INLINE point #-}

data ThunkStore l v = forall m. TS Int (Map.Map ScpVarIndex Ptr') (Map.Map Ptr' (Either (l () -> MC m l v (l v)) (l v)))

newtype MC m l v a = MC {unMC :: ThunkStore l v -> m (ThunkStore l v, a)}

instance (Functor m) => Functor (MC m l v) where
   fmap f (MC x) = MC $ \th -> fmap (fmap f) (x th)
   {-# INLINE fmap #-}

showTS :: (Show (l v)) => ThunkStore l v -> String
showTS (TS i _ m) = show i ++ " " ++ concatMap ((++ "\n") . show) (rights $ map snd (Map.toList m)) ++ "\n" ++ show (length (rights $ map snd (Map.toList m))) ++ " " ++ show (length (lefts $ map snd (Map.toList m)))
{-# INLINE showTS #-}

instance (Show (l v)) => Show (ThunkStore l v) where
   show = showTS


-- data LocalBindings

-- instance Identify LocalBindings where
   --  identify = "LocalBindings"

-- type Ptrs = Map.Map ScpVarIndex Ptr

-- type Let sig sigl a =
   --  (Thunking a :<<<<: sigl)

lvar
    :: (Thunking a :<<<<: sigl, EffectCons m sig sigs sigl Id)
    => Scope
    -> VarIndex
    -> m a
lvar scope i =
    logCall >> force (Right (scope, i))
{-# INLINE lvar #-}

let'
    :: (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => Scope
    -> [(VarIndex, m a)]
    -> m a
    -> m a
let' scope bs e =
    logCall >> do
        let (vs, ps) = unzip bs
        ptrs <- mapM thunk ps
        letThunked scope (zip vs ptrs) e
{-# INLINE let' #-}

letThunked
    :: forall m sig sigs sigl a. (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => Scope
    -> [(VarIndex, Ptr')]
    -> m a
    -> m a
letThunked _ [] e = logCall >> e
letThunked scope bs e =
    logCall >> do
        let (vs, ptrs) = unzip bs
            vs' = map (scope,) vs
        addBindings @a (zip vs' ptrs)
        e
{-# INLINE letThunked #-}