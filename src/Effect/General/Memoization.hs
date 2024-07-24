{-# LANGUAGE AllowAmbiguousTypes #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE DeriveFunctor #-}
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
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda using `infix`" #-}

module Effect.General.Memoization where

import Debug (ctrace)
import Free

import Data.Bifunctor (second)
import Data.IntMap (IntMap, (!))
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Effect.General.State (StateL (..))
import Signature

data Thunking v :: Type -> (Type -> Type) -> Type where
   Thunk :: Thunking v Ptr (OneSub v)
   Force :: Ptr -> Thunking v v NoSub

thunk
   :: forall sig sigs sigl v
    . (Thunking v :<<<<: sigl, Functor sig, Functor sigs)
   => Prog (Sig sig sigs sigl Id) v
   -> Prog (Sig sig sigs sigl Id) Ptr
thunk t = ctrace "thunk" $ injectL (Thunk :: Thunking v Ptr (OneSub v)) (Id ()) (\One _ -> fmap Id t) (Return . unId)

force :: (Thunking v :<<<<: sigl) => Ptr -> Prog (Sig sig sigs sigl Id) v
force p = ctrace ("force " ++ show p) $ injectL (Force p) (Id ()) (\x -> case x of {}) (Return . unId)

type Ptr = Int
type Thunk sig sigs sigl l v = Either (l () -> H v sig sigs sigl l (l v)) (l v)
type ThunkStore sig sigs sigl l v = (Int, IntMap (Thunk sig sigs sigl l v))

runLazy :: (Functor sig, Functor sigs, Functor l, Show (l v), Show (l ())) => ThunkStore sig sigs sigl l v -> Prog (Sig sig sigs (Thunking v :+++: sigl) l) b -> Prog (Sig sig sigs sigl (StateL (ThunkStore sig sigs sigl l v) l)) b
runLazy s = fmap snd . \p -> hLazy p s

hLazy
   :: forall sig sigs sigl l v a
    . (Functor sig, Functor sigs, Functor l, Show (l v), Show (l ()))
   => Prog (Sig sig sigs (Thunking v :+++: sigl) l) a
   -> ThunkStore sig sigs sigl l v
   -> Prog (Sig sig sigs sigl (StateL (ThunkStore sig sigs sigl l v) l)) (ThunkStore sig sigs sigl l v, a)
hLazy = ctrace "runMemo" . unH . fold point (lalg algM)
  where
   algM
      :: Thunking v p c
      -> l ()
      -> (forall x. c x -> l () -> H v sig sigs sigl l (l x))
      -> (l p -> H v sig sigs sigl l b)
      -> H v sig sigs sigl l b
   algM Thunk l st k = H $ \(fresh, im) -> ctrace ("thunked " ++ show fresh) $ unH (k (fresh <$ l)) (fresh + 1, IntMap.insert fresh (Left (st One)) im)
   algM (Force p) l _ k = H $ \th -> ctrace ("forcelookup " ++ show (IntMap.keys $ snd th)) $ case snd th ! p of
      Left t -> ctrace ("evaluate " ++ show p ++ ": " ++ show l) $ do
         (th', lv) <- unH (t l) th
         unH (k lv) (second (IntMap.insert p (Right lv)) th')
      Right lv -> ctrace ("memoized " ++ show p ++ ": " ++ show lv ++ show l) $ unH (k lv) th

data H v sig sigs sigl l a = H
   { unH
      :: ThunkStore sig sigs sigl l v
      -> Prog (Sig sig sigs sigl (StateL (ThunkStore sig sigs sigl l v) l)) (ThunkStore sig sigs sigl l v, a)
   }
   deriving (Functor)

instance (Functor sig, Functor sigs) => Pointed (H v sig sigs sigl l) where
   point x = H $ \th -> return (th, x)

instance Forward (H v) where
   afwd op = H $ \th -> Call $ A $ Algebraic $ fmap (\x -> unH x th) op
   sfwd op = H $ \th -> Call $ S $ Enter $ fmap (go th) op
     where
      go th hhx = do
         (th', hx) <- unH hhx th
         return (unH hx th')
   lfwd op l st k = H $ \th ->
      Call $
         L $
            Node
               op
               (StateL (th, l))
               (\c (StateL (th', lv)) -> StateL <$> unH (st c lv) th')
               (\(StateL (th', lv)) -> unH (k lv) th')