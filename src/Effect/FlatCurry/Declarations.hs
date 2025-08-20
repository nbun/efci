{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Effect.FlatCurry.Declarations (
    DeclF (..),
    getBody,
    H,
    runDecl,
    initDecls,
    runDeclSmart,
    runDeclC,
    Progs (..),
) where

import Control.Monad (ap, void)
import Curry.FlatCurry.Annotated.Type (ARule (AExternal), QName, TypeExpr, VarIndex, Visibility)
import qualified Data.Map as Map
import Debug.Trace (trace, traceShowId)
import Effect.General.State (EffectCons, logCall)
import Free
import Signature
import Type (AEFuncDecl (AEFunc), AEProg (..), fdclBody)

data DeclF v :: * -> (* -> *) -> * where
    DeclBody :: QName -> DeclF v v NoSub
    Init :: [AEProg ()] -> DeclF v () (ManySub v)

data ManySub v :: * -> * where
    Many :: QName -> ManySub v v

newtype Progs (l :: * -> *) (v :: *) (m :: * -> *) = Progs {unProgs :: [AEProg (l () -> H (Progs l v m) m (l v))]}

newtype H r m a = H {unH :: r -> m a}

instance (Functor m) => Functor (H (Progs l v m) m) where
    fmap f (H x) = H $ \th -> fmap f (x th)
    {-# INLINE fmap #-}

runDecl :: (EffectCons m sig sigs sigl l) => Progs l v m -> Prog (Sig sig sigs (DeclF v :+++: sigl) l) a -> m a
runDecl s p = hDecl p s
{-# INLINE runDecl #-}

hDecl
    :: (EffectCons m sig sigs sigl l)
    => Prog (Sig sig sigs (DeclF v :+++: sigl) l) a
    -> Progs l v m
    -> m a
hDecl = unH . fold point con
{-# INLINE hDecl #-}

runDeclSmart :: (EffectCons m sig sigs sigl l) => Progs l v m -> SmartProg (Sig sig sigs (DeclF v :+++: sigl) l) a -> m a
runDeclSmart s p = hDeclSmart p s
{-# INLINE runDeclSmart #-}

hDeclSmart
    :: (EffectCons m sig sigs sigl l)
    => SmartProg (Sig sig sigs (DeclF v :+++: sigl) l) a
    -> Progs l v m
    -> m a
hDeclSmart = unH . smartFold point con
{-# INLINE hDeclSmart #-}

addBody :: (ManySub v v -> l () -> H (Progs l v m) m (l v)) -> AEFuncDecl a -> AEFuncDecl (l () -> H (Progs l v m) m (l v))
addBody get (AEFunc qn ar vis ty _) = AEFunc qn ar vis ty (get (Many qn))

instance ReaderCarrier (H (Progs l v m)) (Progs l v m)
instance DeriveForward 'Reader (H (Progs l v m)) VoidL

algDecl
    :: (Monad m)
    => Latent (DeclF v) l (H (Progs l v m) m) (H (Progs l v m) m a)
    -> H (Progs l v m) m a
algDecl (Node op l st' k') = H $ \th ->
    let k = unH . k'
     in case op of
            DeclBody qn -> do
                lv <- (unH . fdclBody (findModule (unProgs th) qn)) l th
                k lv th
            Init ps ->
                let th' = Progs $ map (\(AEProg mod imp tdecls fdecls opdecls) -> AEProg mod imp tdecls (Map.map (addBody st') fdecls) opdecls) ps
                 in k l th'

instance (EffectMonad m sig sigs sigl l) => TermAlgebra (H (Progs l v m) m) (Sig sig sigs (DeclF v :+++: sigl) l) where
    con (A op) = afwd @VoidL op
    con (S op) = sfwd @VoidL op
    con (L (Node op l st k)) = case op of
        (Inl3 op') -> algDecl (Node op' l st k)
        (Inr3 op') -> lfwd @VoidL @'Reader (Node op' l st k)
    {-# INLINE con #-}
    var = H . (\x _ -> return x)
    {-# INLINE var #-}

runDeclC :: (EffectMonad m sig sigs sigl l) => Progs l v m -> Cod (H (Progs l v m) m) a -> m a
runDeclC th p = unH (runCod var p) th
{-# INLINE runDeclC #-}

instance (Pointed m) => Pointed (H (Progs l v m) m) where
    point x = H $ \_ -> point x
    {-# INLINE point #-}

getBody
    :: forall sig sigs sigl m a
     . (EffectCons m sig sigs sigl Id)
    => (DeclF a :<<<<: sigl)
    => QName -> m a
getBody qn = logCall >> injectL (DeclBody qn :: DeclF a _ _) (Id ()) (\x -> case x of {}) (return . unId)
{-# INLINE getBody #-}

initDecls
    :: forall sig sigs sigl m v
     . (DeclF v :<<<<: sigl, EffectCons m sig sigs sigl Id)
    => [AEProg (m v)] -> m ()
initDecls ps = logCall >> injectL (Init (map void ps) :: DeclF v _ _) (Id ()) (\(Many qn) _ -> fmap Id (fdclBody $ findModule ps qn)) (const (return ()))
{-# INLINE initDecls #-}

findModule :: [AEProg a] -> QName -> AEFuncDecl a
findModule ps qn@(mod, _) = case res of
    Just fdecl -> fdecl
    Nothing -> error $ "Function declaration " ++ show qn ++ " not found"
  where
    res =
        foldr
            ( \(AEProg name _ _ fdecls _) acc ->
                if name == mod
                    then findFuncDecl fdecls qn
                    else acc
            )
            Nothing
            ps

findFuncDecl :: Map.Map QName (AEFuncDecl a) -> QName -> Maybe (AEFuncDecl a)
findFuncDecl m qn = Map.lookup qn m
{-# INLINE findFuncDecl #-}