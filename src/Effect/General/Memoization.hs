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

module Effect.General.Memoization where

import Debug (ctrace)
import Free

import Data.Bifunctor (second)
import Data.Either (rights)
import Data.IntMap (IntMap, (!))
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Effect.General.State (StateL (..))
import Signature

data Thunking v :: Type -> (Type -> Type) -> Type where
   Thunk :: Thunking v Ptr (OneSub v)
   Force :: Ptr -> Thunking v v NoSub

thunk
   :: forall m sig sigs sigl v
    . (EffectMonad m sig sigs sigl Id, Thunking v :<<<<: sigl)
   => m v
   -> m Ptr
thunk t = ctrace "thunk" $ injectL (Thunk :: Thunking v Ptr (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
{-# INLINE thunk #-}

force :: (EffectMonad m sig sigs sigl Id, Thunking v :<<<<: sigl) => Ptr -> m v
force p = ctrace ("force " ++ show p) $ injectL (Force p) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE force #-}

type Ptr = Int

runLazy :: (Functor sig, Functor sigs, Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore n l v) l)), n ~ Prog (Sig sig sigs sigl l), Monad m) => ThunkStore m l v -> Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazy s = fmap snd . \p -> hLazy p s
{-# INLINE runLazy #-}

hLazy
   :: forall m n sig sigs sigl l v a
    . (Functor sig, Functor sigs, Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore n l v) l)), n ~ Prog (Sig sig sigs sigl l), Monad m)
   => Prog (Sig sig sigs (Thunking v :+++: sigl) l) a
   -> ThunkStore m l v
   -> m (ThunkStore m l v, a)
hLazy = ctrace "runMemo" . unMC . fold point con
{-# INLINE hLazy #-}

instance (Functor l, EffectMonad n sig sigs sigl l, EffectMonad m sig sigs sigl (StateL (ThunkStore n l v) l), Show (l v)) => TermAlgebra (MC m l v) (Sig sig sigs (Thunking v :+++: sigl) l) where
   con (A (Algebraic op)) = MC $ \th -> con $ A $ Algebraic $ fmap (\x -> unMC x th) op
   con (S (Enter op)) = MC $ \th -> con $ S $ Enter $ fmap (go th) op
     where
      go th hhx = do
         (th', hx) <- unMC hhx th
         return (unMC hx th')
   con (L (Node (Inl3 Thunk) l st k)) = MC $ \(fresh, im) -> ctrace ("thunked " ++ show fresh) $ unMC (k (fresh <$ l)) (fresh + 1, IntMap.insert fresh (Left (st One)) im)
   con (L (Node (Inl3 (Force p)) l _ k)) = MC $ \th -> ctrace ("forcelookup " ++ show (IntMap.keys $ snd th)) $ case snd th ! p of
      Left t -> do
         (th', lv) <- unMC (t l) th
         unMC (k lv) (ctrace ("evaluate " ++ show p ++ show lv) $ (second (IntMap.insert p (Right lv)) th'))
      Right lv -> ctrace ("memoized " ++ show p ++ show lv) $ unMC (k lv) th
   -- con (L (Node (Inr3 op) l st k)) = MC $ \th ->
   --    con $
   --       L $
   --          Node
   --             op
   --             (StateL (th, l))
   --             (\c (StateL (th', lv)) -> StateL <$> unMC (st c lv) th')
   --             (\(StateL (th', lv)) -> unMC (k lv) th')
   {-# INLINE con #-}
   var = MC . gen'Memo
     where
      gen'Memo x th = return (th, x)
   {-# INLINE var #-}

runLazyC :: (EffectMonad n sig sigs sigl l, EffectMonad m sig sigs sigl (StateL (ThunkStore n l v) l), Functor l, Show (l v)) => ThunkStore m l v -> Cod (MC m l v) a -> m a
runLazyC th p = (\(s, r) -> ctrace (showTS s) r) <$> unMC (runCod var p) th
-- runLazyC th p = snd <$> unMC (runCod var p) th
{-# INLINE runLazyC #-}

instance (Monad m) => Pointed (MC m l v) where
   point x = MC $ \th -> return (th, x)
   {-# INLINE point #-}

type Thunk m l v = Either (l () -> MC m l v (l v)) (l v)

type ThunkStore m l v = (Int, IntMap (Thunk m l v))

newtype MC m l v a = MC {unMC :: ThunkStore m l v -> m (ThunkStore m l v, a)}

instance (Functor m) => Functor (MC m l v) where
   fmap f (MC x) = MC $ \th -> fmap (fmap f) (x th)
   {-# INLINE fmap #-}

showTS :: (Show (l v)) => ThunkStore m l v -> String
showTS (i, m) = show i ++ " " ++ show (rights $ map snd (IntMap.toList m))