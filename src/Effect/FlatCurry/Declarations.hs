{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds #-}


{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PartialTypeSignatures #-}


module Effect.FlatCurry.Declarations (DeclF, runDecl, runDeclC, H (..), initDecls, getBody, getInfo) where

import Debug (ctrace)
import Type (AEProg (..), AEFuncDecl (AEFunc), fdclBody, fdclVars, AERule (AERule, AEExternal))
import Curry.FlatCurry.Annotated.Type (QName, VarIndex, TypeExpr, Visibility, ARule (AExternal))
import qualified Data.Map as Map
import Control.Monad (ap, void)
import Signature
import Free

data DeclF v :: * -> (* -> *) -> * where
  DeclInfo  :: QName ->  DeclF v (Int, Visibility, TypeExpr, AERule ()) NoSub
  DeclBody  :: QName ->  DeclF v v                                      NoSub
  Init      :: [AEProg ()]   ->  DeclF v ()                             (ManySub v)

data ManySub v  :: * -> *
   where Many :: QName -> ManySub v v

type Progs m l v = [AEProg (H m l v (l v))]

newtype H m l v a = H { unH :: Progs m l v -> m a }

instance (Functor m) => Functor (H m l v) where
  fmap f (H x) = H $ \th -> fmap f (x th)
  {-# INLINE fmap #-}

runDecl :: (Functor l, m ~ Prog (Sig sig sigs sigl l), Functor sig, Functor sigs) => Progs m l v -> Prog (Sig sig sigs (DeclF v :+++: sigl) l) b -> m b
runDecl s p = hDecl p s
{-# INLINE runDecl #-}

hDecl  :: forall sig sigs sigl l m v a. (Functor l, m ~ Prog (Sig sig sigs sigl l), Functor sig, Functor sigs) => Prog (Sig sig sigs (DeclF v :+++: sigl) l) a
      -> Progs m l v
      -> m a
hDecl  = ctrace "runDecl" . unH . fold point con
{-# INLINE hDecl #-}

addBody :: (ManySub v v -> H m l v (l v)) -> AEFuncDecl a -> AEFuncDecl (H m l v (l v))
addBody get (AEFunc qn ar vis ty (AERule vs _)) = AEFunc qn ar vis ty (AERule vs (get (Many qn)))
addBody _   (AEFunc qn ar vis ty (AEExternal s)) = AEFunc qn ar vis ty (AEExternal s)

instance (Functor l, EffectMonad m sig sigs sigl l) => TermAlgebra (H m l v) (Sig sig sigs (DeclF v :+++: sigl) l) where
  con (A (Algebraic op)) = H $ \th -> con $ A $ Algebraic $ fmap (\x -> unH x th) op
  con (S (Enter op)) = H $ \th -> con $ S $ Enter $ fmap (go th) op
      where go th hhx = do
                 hx <- unH hhx th
                 return (unH hx th)
  con (L (Node (Inl3 (DeclInfo qn)) l _ k)) = H $ \th -> do
    let (AEFunc _ ar vis ty r) = findModule th qn
    unH (k ((ar, vis, ty, void r) <$ l)) th
  con (L (Node (Inl3 (DeclBody qn)) _ _ k)) = H $ \th -> do
           lv <- unH (fdclBody $ findModule th qn) th
           unH (k lv) th
  con (L (Node (Inl3 (Init ps)) l st k)) = H $ \_ -> do
           let th' = map (\(AEProg mod imp tdecls fdecls opdecls) -> AEProg mod imp tdecls (Map.map (addBody (`st` l)) fdecls) opdecls) ps
           unH (k l) th'
  con (L (Node (Inr3 op) l st k)) = H $ \th ->  con $ L $
                    Node op l
                             (\c lv -> unH (st c lv) th)
                             (\lv -> unH (k lv) th)
  {-# INLINE con #-}
  var = H . gen'Memo
    where gen'Memo x _ = return x
  {-# INLINE var #-}

runDeclC :: (EffectMonad m sig sigs sigl l, Functor l) => Progs m l v -> Cod (H m l v) a -> m a
runDeclC th p = unH (runCod var p) th
{-# INLINE runDeclC #-}

instance (Monad m) => Pointed (H m l v) where
   point x = H $ \_ -> return x
   {-# INLINE point #-}

getInfo :: forall a sig sigs sigl m.
    (EffectMonad m sig sigs sigl Id)
    => (DeclF a :<<<<: sigl)
    => QName -> m (Int, Visibility, TypeExpr, AERule ())
getInfo qn = ctrace "ask" $ injectL (DeclInfo qn :: DeclF a _ _) (Id ()) (\x -> case x of) (return . unId)
{-# INLINE getInfo #-}

getBody :: forall sig sigs sigl m a.
    (EffectMonad m sig sigs sigl Id)
    => (DeclF a :<<<<: sigl)
    => QName -> m a
getBody qn = ctrace "ask" $ injectL (DeclBody qn :: DeclF a _ _) (Id ()) (\x -> case x of) (return . unId)
{-# INLINE getBody #-}

initDecls :: forall sig sigs sigl m v.
         (DeclF v :<<<<: sigl, EffectMonad m sig sigs sigl Id)
      => [AEProg (m v)] -> m ()
initDecls ps = injectL (Init (map void ps) :: DeclF v _ _) (Id ()) (\(Many qn) _ -> fmap Id (fdclBody $ findModule ps qn)) (const (return ()))
{-# INLINE initDecls #-}

findModule :: [AEProg a] -> QName -> AEFuncDecl a
findModule ps qn@(mod, _) = case res of
  Just fdecl -> fdecl
  Nothing    -> error $ "Function declaration " ++ show qn ++ " not found"
  where
    res = foldr
      (\(AEProg name _ _ fdecls _) acc -> if name == mod
                                          then findFuncDecl fdecls qn
                                          else acc)
      Nothing
      ps

findFuncDecl :: Map.Map QName (AEFuncDecl a) -> QName -> Maybe (AEFuncDecl a)
findFuncDecl m qn = Map.lookup qn m
{-# INLINE findFuncDecl #-}