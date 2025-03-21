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

module Effect.General.Delay where

import Free

import Data.Kind (Type)
import Effect.General.State (StateL (..), EffectCons, logCall, Scope)
import Signature
import Debug (ctrace, strace)
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.IntMap as IntMap
import Data.IntMap ((!))
import Curry.FlatCurry (VarIndex)
import Effect.General.Memoization (Ptr)

data Delaying v :: Type -> (Type -> Type) -> Type where
   Delay :: Delaying v Ptr (OneSub v)
   Retrieve :: Ptr -> Delaying v v NoSub

delay
   :: forall m sig sigs sigl v
    . (EffectCons m sig sigs sigl Id, Delaying v :<<<<: sigl)
   => m v
   -> m Ptr
delay t = logCall >> injectL (Delay :: Delaying v Ptr (OneSub v)) (Id ()) (\One _ -> fmap Id t) (return . unId)
{-# INLINE delay #-}

retrieve :: (EffectCons m sig sigs sigl Id, Delaying v :<<<<: sigl) => Ptr -> m v
retrieve e = logCall >> injectL (Retrieve e) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE retrieve #-}

-- transfer :: (EffectCons m sig sigs sigl Id, Delaying v :<<<<: sigl) => [Ptr] -> m ()
-- transfer ptrs = logCall >> do
   -- es <- mapM retrieve ptrs
   -- mapM_ thunk es

runDelay :: (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (DelayStore l v) l)), Monad m, Vars (l v)) => Prog (Sig sig sigs (Delaying v :+++: sigl) l) b -> m b
runDelay = fmap snd . \p -> hDelay p (TS 0 IntMap.empty)
{-# INLINE runDelay #-}

runDelaySmart :: (Functor l, Show (l v), Show (l ()), m ~ SmartProg (Sig sig sigs sigl (StateL (DelayStore l v) l)), Monad m, Vars (l v)) => SmartProg (Sig sig sigs (Delaying v :+++: sigl) l) b -> m b
runDelaySmart = fmap (\(s, r) -> strace (showTS s) r)  . \p -> hDelaySmart p (TS 0 IntMap.empty)
{-# INLINE runDelaySmart #-}

hDelay
   :: forall m n sig sigs sigl l v a
    . (Functor l, Show (l v), Show (l ()), m ~ Prog (Sig sig sigs sigl (StateL (DelayStore l v) l)), Monad m, Vars (l v))
   => Prog (Sig sig sigs (Delaying v :+++: sigl) l) a
   -> DelayStore l v
   -> m (DelayStore l v, a)
hDelay = unDC . fold point con
{-# INLINE hDelay #-}

hDelaySmart
   :: forall m n sig sigs sigl l v a
    . (Functor l, Show (l v), Show (l ()), m ~ SmartProg (Sig sig sigs sigl (StateL (DelayStore l v) l)), Monad m, Vars (l v))
   => SmartProg (Sig sig sigs (Delaying v :+++: sigl) l) a
   -> DelayStore l v
   -> m (DelayStore l v, a)
hDelaySmart = unDC . smartFold point con
{-# INLINE hDelaySmart #-}

instance (Functor l, EffectMonad m sig sigs sigl (StateL (DelayStore l v) l), Show (l v), Vars (l v)) => TermAlgebra (DC m l v) (Sig sig sigs (Delaying v :+++: sigl) l) where
   con (A (Algebraic op)) = DC $ \th -> con $ A $ Algebraic $ fmap (\x -> unDC x th) op
   con (S (Enter op)) = DC $ \th -> con $ S $ Enter $ fmap (go th) op
     where
      go th hhx = do
         (th', hx) <- unDC hhx th
         return (unDC hx th')
   con (L (Node (Inl3 Delay) l st k)) = DC $ \(TS fresh im) -> ctrace ("delayed " ++ show fresh) $ unDC (k (fresh <$ l)) (TS (fresh + 1) (IntMap.insert fresh (unsafeCoerce $ st One) im))
   con (L (Node (Inl3 (Retrieve p)) l _ k)) = DC $ \ts@(TS fresh th) -> ctrace ("retrievelookup " ++ show (IntMap.keys th)) $ do
         unDC (unsafeCoerce $ (th ! p) l) (TS fresh (IntMap.delete p th))
   con (L (Node (Inr3 op) l st k)) = DC $ \th ->
      con $
         L $
            Node
               op
               (StateL (th, l))
               (\c (StateL (th', lv)) -> StateL <$> unDC (st c lv) th')
               (\(StateL (th', lv)) -> unDC (k lv) th')
   {-# INLINE con #-}
   var = DC . gen'Memo
     where
      gen'Memo x th = return (th, x)
   {-# INLINE var #-}

runDelayC :: (EffectMonad m sig sigs sigl (StateL (DelayStore l v) l), Functor l, Show (l v), Vars (l v)) => Cod (DC m l v) a -> m a
runDelayC p = (\(s, r) -> ctrace (showTS s) r) <$> unDC (runCod var p) (TS 0 IntMap.empty)
-- runDelayC th p = snd <$> unDC (runCod var p) th
{-# INLINE runDelayC #-}

instance (Monad m) => Pointed (DC m l v) where
   point x = DC $ \th -> return (th, x)
   {-# INLINE point #-}

data DelayStore l v = forall m. TS Int (IntMap.IntMap ((l () -> DC m l v (l v))))

newtype DC m l v a = DC {unDC :: DelayStore l v -> m (DelayStore l v, a)}

instance (Functor m) => Functor (DC m l v) where
   fmap f (DC x) = DC $ \th -> fmap (fmap f) (x th)
   {-# INLINE fmap #-}

showTS :: (Show (l v)) => DelayStore l v -> String
showTS (TS i m) = show i ++ " \n"
  ++ concatMap ((++ "\n") . show . (\(i, _) -> (i, ("-")))) ((IntMap.toList m))
  ++ " delays: " ++ show (length (map snd (IntMap.toList m)))
{-# INLINE showTS #-}

instance (Show (l v)) => Show (DelayStore l v) where
   show = showTS