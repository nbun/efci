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

import Free

import Data.Bifunctor (second)
import Data.Either (rights)
import Data.IntMap (IntMap, (!))
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Effect.General.State (StateL (..), EffectCons, logCall)
import Signature
import Debug (ctrace)
import Unsafe.Coerce (unsafeCoerce)

data Thunking v :: Type -> (Type -> Type) -> Type where
   Thunk :: Thunking v Ptr (OneSub v)
   Force :: Ptr -> Thunking v v NoSub

thunk
   :: forall m sig sigs sigl v
    . (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl)
   => m v
   -> m Ptr
thunk t = logCall >> injectL (Thunk :: Thunking v Ptr (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
{-# INLINE thunk #-}

force :: (EffectCons m sig sigs sigl Id, Thunking v :<<<<: sigl) => Ptr -> m v
force p = logCall >> injectL (Force p) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE force #-}

type Ptr = Int

runLazy :: (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m) => Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> m b
runLazy = fmap snd . \p -> hLazy p (TS 0 IntMap.empty)
{-# INLINE runLazy #-}

hLazy
   :: forall m n sig sigs sigl l v a
    . (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (ThunkStore l v) l)), Monad m)
   => Prog (Sig sig sigs (Thunking v :+++: sigl) l) a
   -> ThunkStore l v
   -> m (ThunkStore l v, a)
hLazy = unMC . fold point con
{-# INLINE hLazy #-}

instance (Functor l, EffectMonad m sig sigs sigl (StateL (ThunkStore l v) l), Show (l v)) => TermAlgebra (MC m l v) (Sig sig sigs (Thunking v :+++: sigl) l) where
   con (A (Algebraic op)) = MC $ \th -> con $ A $ Algebraic $ fmap (\x -> unMC x th) op
   con (S (Enter op)) = MC $ \th -> con $ S $ Enter $ fmap (go th) op
     where
      go th hhx = do
         (th', hx) <- unMC hhx th
         return (unMC hx th')
   con (L (Node (Inl3 Thunk) l st k)) = MC $ \(TS fresh im) -> ctrace ("thunked " ++ show fresh) $ unMC (k (fresh <$ l)) (TS (fresh + 1) (IntMap.insert fresh (Left (unsafeCoerce $ st One)) im))
   con (L (Node (Inl3 (Force p)) l _ k)) = MC $ \ts@(TS _ th) -> ctrace ("forcelookup " ++ show (IntMap.keys th)) $ case th ! p of
      Left t -> do
         (TS fresh' th', lv) <- unMC (unsafeCoerce $ t l) ts
         unMC (k lv) (ctrace ("evaluate " ++ show p ++ show lv) (TS fresh' (IntMap.insert p (Right lv) th')))
      Right lv -> ctrace ("memoized " ++ show p ++ show lv) $ unMC (k lv) ts
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
runLazyC p = (\(s, r) -> ctrace (showTS s) r) <$> unMC (runCod var p) (TS 0 IntMap.empty)
-- runLazyC th p = snd <$> unMC (runCod var p) th
{-# INLINE runLazyC #-}

instance (Monad m) => Pointed (MC m l v) where
   point x = MC $ \th -> return (th, x)
   {-# INLINE point #-}

data ThunkStore l v = forall m. TS Int (IntMap (Either (l () -> MC m l v (l v)) (l v)))

newtype MC m l v a = MC {unMC :: ThunkStore l v -> m (ThunkStore l v, a)}

instance (Functor m) => Functor (MC m l v) where
   fmap f (MC x) = MC $ \th -> fmap (fmap f) (x th)
   {-# INLINE fmap #-}

showTS :: (Show (l v)) => ThunkStore l v -> String
showTS (TS i m) = show i ++ " " ++ show (rights $ map snd (IntMap.toList m))

instance (Show (l v)) => Show (ThunkStore l v) where
   show = showTS