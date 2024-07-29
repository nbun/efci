{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Effect.FlatCurry.Constructor where

import Control.Monad (void)
import Curry.FlatCurry.Annotated.Type (APattern (..), Literal (..), VarIndex)
import Curry.FlatCurry.Type (CaseType (..), QName)
import Data.Functor ((<&>))
import Data.Maybe (mapMaybe)
import Debug (ctrace)
import Effect.FlatCurry.Let
import Effect.General.Error (Err (..))
import Effect.General.Memoization (Ptr, Thunking, force, thunk)
import Effect.General.ND (ND, choose, failed)
import Effect.General.State
import Free
import Signature

data ConsF a
  = FCons QName [Ptr]
  | FStrictCons QName [a]
  | FLit Literal
  | FFree VarIndex
  deriving (Functor)

data CaseScope a
  = Case a (Value () -> a)
  | Normalize a ((QName, [Ptr]) -> a)
  | External [a] ([Value ()] -> a)
  | Unify a a ((Value (), Value ()) -> a)
  deriving (Functor)

data Mode
  = Strict
  | Lazy CaseType
  deriving (Eq, Show)

normalform
  :: ( ConsF :<: sig
     , Thunking a :<<<<: sigl
     , CaseScope :<: sigs
     , Functor sig
     , Functor sigs
     )
  => Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
normalform (Return x) = Return x
normalform p = ctrace "normalform" $
  do
    Call $ S $ Enter $ inj (Normalize (fmap return p) (fmap return . f))
 where
  f (qn, ptrs) = do
    let args = map (normalform . force) ptrs
    Call $ A $ Algebraic $ inj (FStrictCons qn args)

cons
  :: (Functor sig, Functor sigs, Thunking a :<<<<: sigl, ConsF :<: sig)
  => QName
  -> [Prog (Sig sig sigs sigl Id) a]
  -> Prog (Sig sig sigs sigl Id) a
cons qn ps = do
  args <- mapM thunk ps
  ctrace ("cons " ++ show qn ++ " with " ++ show args) $
    Call $
      A $
        Algebraic $
          inj (FCons qn args)

thunkedCons
  :: (Functor sig, Functor sigs, Thunking a :<<<<: sigl, ConsF :<: sig)
  => QName
  -> [Ptr]
  -> Prog (Sig sig sigs sigl Id) a
thunkedCons qn args = do
  ctrace ("thunkedCons " ++ show qn ++ " with " ++ show args) $
    Call $
      A $
        Algebraic $
          inj (FCons qn args)

lit :: (ConsF :<: sig) => Literal -> Prog (Sig sig sigs sigl l) v
lit l = Call (A (Algebraic (inj (FLit l))))

data CaseState

instance Identify CaseState where
  identify = "CaseState"

case'
  :: forall sig sigs sigl a
   . (Let sig sigl a, CaseScope :<: sigs, ND :<: sig, ConstraintStore :<: sig, ConsF :<: sig)
  => Scope
  -> Prog (Sig sig sigs sigl Id) a
  -> [(APattern (), Prog (Sig sig sigs sigl Id) a)]
  -> Prog (Sig sig sigs sigl Id) a
case' scope cp brs =
  ctrace "case" $
    injectS (Case (fmap return cp) (return . cnt))
 where
  cnt :: Value () -> Prog (Sig sig sigs sigl Id) a
  cnt hnf = case mapMaybe (match hnf) brs of
    [] -> failed
    [x] -> x
    xs -> choose xs
   where
    match (HNF qn args) (APattern _ (pqn, _) argVars, e)
      | pqn == qn =
          ctrace
            ("Pattern match! " ++ show qn ++ " with " ++ show args)
            $ Just
            $ letThunked scope (zip (map fst argVars) args) e
      | otherwise =
          ctrace
            ("Pattern match failed: " ++ show qn ++ " mismatches " ++ show pqn)
            Nothing
    match (Lit l) (ALPattern _ lp, e)
      | l == lp = Just e
      | otherwise = Nothing
    match (Free i) pat = Just $ do
      case pat of
        (APattern _ (pqn, _) argVars, e) -> do
          cs <- get @CStore
          vs <- freshNames scope (length argVars)
          let fvs = map (fvar scope) vs
          put @CStore (addC i (ConsC pqn vs) cs)
          let' scope (zip (map fst argVars) fvs) e
        (ALPattern _ lp, e) -> do
          cs <- get @CStore
          put @CStore (addC i (LitC lp) cs)
          e
    match v ps =
      error $
        "Pattern match not implemented for " ++ show v ++ show (fst ps)

data Value a
  = Cons QName [Value a]
  | HNF QName [Ptr]
  | Lit Literal
  | Free VarIndex
  | ValOther a
  deriving (Functor, Show)

newtype ValueL l a = ValueL {unValueL :: Value (l a)}
  deriving (Functor, Show)

runCons
  :: forall sig sigs sigl l a
   . (Functor sig, Functor sigs)
  => Prog (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l) a
  -> Prog (Sig sig sigs sigl (ValueL l)) (Value a)
runCons = ctrace "runCons" . unC . fold point (asalg algCa algCs)
 where
  algCa :: ConsF (C sig sigs sigl l x) -> C sig sigs sigl l x
  algCa (FCons qn args) = C $ return (HNF qn args)
  algCa (FStrictCons qn args) = C (mapM unC args <&> Cons qn)
  algCa (FLit l) = C $ return (Lit l)
  algCa (FFree i) = C $ return (Free i)

  algCs :: CaseScope (C sig sigs sigl l (C sig sigs sigl l x)) -> C sig sigs sigl l x
  algCs (Case ce k) = C $
    do
      hnf <- unC ce
      unC (k (void hnf)) >>= lift'
  algCs (Normalize ce k) = C $
    do
      hnf <- unC ce
      case hnf of
        HNF qn args -> do
          hnf <- unC (k (qn, args))
          case hnf of
            Cons qn args -> mapM lift' args <&> Cons qn
            Lit l -> return $ Lit l
            _ -> undefined
        Lit l -> return $ Lit l
        Free i -> return $ Free i
        Cons qn args -> mapM lift' args <&> Cons qn
        ValOther x -> unC x
  algCs (External ps k) = C $
    do
      hnfs <- mapM unC ps
      hnf <- unC $ k (map void hnfs)
      lift' hnf
  algCs (Unify e1 e2 k) = C $
    do
      hnf1 <- unC e1
      hnf2 <- unC e2
      hnf <- unC (k (void hnf1, void hnf2))
      lift' hnf

  lift'
    :: Value (C sig sigs sigl l x)
    -> Prog (Sig sig sigs sigl (ValueL l)) (Value x)
  lift' = lift . fmap unC

newtype C sig sigs sigl l a = C {unC :: Prog (Sig sig sigs sigl (ValueL l)) (Value a)}
  deriving (Functor)

instance Forward C where
  afwd op = C $ Call $ A $ Algebraic $ fmap unC op
  sfwd op = C $ Call $ S $ Enter $ fmap (fmap lift . unC . fmap unC) op
  lfwd op l st k = C $ Call $ L $ Node op (ValueL $ ValOther l) (st' st) k'
   where
    st' st2 c l' = lift2 (fmap (\x -> ValueL <$> unC (st2 c x)) (unValueL l'))
    k' = lift . fmap (unC . k) . unValueL

instance Lift ValueL Value where
  lift (Cons qn args) = mapM lift args <&> Cons qn
  lift (HNF qn ptrs) = return $ HNF qn ptrs
  lift (Lit l) = return $ Lit l
  lift (Free i) = return $ Free i
  lift (ValOther x) = x

  lift2 (Cons qn args) = mapM lift2 args <&> ValueL . Cons qn . map unValueL
  lift2 (HNF qn ptrs) = return $ ValueL $ HNF qn ptrs
  lift2 (Lit l) = return $ ValueL $ Lit l
  lift2 (Free i) = return $ ValueL $ Free i
  lift2 (ValOther x) = x

instance (Functor sig, Functor sigs) => Pointed (C sig sigs sigl l) where
  point x = C $ return (ValOther x)

arithInt
  :: (ConsF :<: sig, CaseScope :<: sigs, Functor sig, Functor sigs)
  => (Integer -> Integer -> Integer)
  -> Prog (Sig sig sigs sigl l) v
  -> Prog (Sig sig sigs sigl l) v
  -> Prog (Sig sig sigs sigl l) v
arithInt op x y =
  Call
    (S (Enter (inj (External [fmap return x, fmap return y] (return . f)))))
 where
  f [Lit (Intc x), Lit (Intc y)] = lit (Intc (x `op` y))

compInt
  :: ( ConsF :<: sig
     , Functor sig
     , Functor sigs
     , Thunking v :<<<<: sigl
     , ConsF :<: sig
     , CaseScope :<: sigs
     )
  => (Integer -> Integer -> Bool)
  -> Prog (Sig sig sigs sigl Id) v
  -> Prog (Sig sig sigs sigl Id) v
  -> Prog (Sig sig sigs sigl Id) v
compInt op x y =
  Call
    (S (Enter (inj (External [fmap return x, fmap return y] (return . f)))))
 where
  f [Lit (Intc x), Lit (Intc y)]
    | x `op` y = cons ("Prelude", "True") []
    | otherwise = cons ("Prelude", "False") []

compChar
  :: ( ConsF :<: sig
     , Functor sig
     , Functor sigs
     , Thunking v :<<<<: sigl
     , ConsF :<: sig
     , CaseScope :<: sigs
     )
  => (Char -> Char -> Bool)
  -> Prog (Sig sig sigs sigl Id) v
  -> Prog (Sig sig sigs sigl Id) v
  -> Prog (Sig sig sigs sigl Id) v
compChar op x y =
  Call
    (S (Enter (inj (External [fmap return x, fmap return y] (return . f)))))
 where
  f [Lit (Charc x), Lit (Charc y)]
    | x `op` y = cons ("Prelude", "True") []
    | otherwise = cons ("Prelude", "False") []

err
  :: ( CaseScope :<: sigs
     , Err :<: sig
     , Functor sig
     , Functor sigs
     , Thunking a :<<<<: sigl
     )
  => Prog (Sig sig sigs sigl Id) a
  -> Prog (Sig sig sigs sigl Id) a
err p = do
  Call $ S $ Enter $ inj (External [fmap return p] (return . f))
 where
  f [hnf] = Call $ A $ Algebraic $ inj (Err (val2str hnf))

val2str :: (Show a) => Value a -> [Char]
val2str (Cons ("Prelude", "[]") []) = ""
val2str (Cons ("Prelude", ":") [Lit (Charc c), xs]) = c : val2str xs
val2str hnf = error $ "hnf2str: " ++ show hnf

str2prog
  :: (Functor sig, Functor sigs, Thunking a :<<<<: sigl, ConsF :<: sig)
  => String
  -> Prog (Sig sig sigs sigl Id) a
str2prog [] = cons ("Prelude", "[]") []
str2prog (c : cs) = cons ("Prelude", ":") [lit (Charc c), str2prog cs]

-- free variables --

fvar
  :: ( ConsF :<: sig
     , Thunking a :<<<<: sigl
     , ConstraintStore :<: sig
     , Renaming :<: sig
     , Functor sigs
     )
  => Scope
  -> VarIndex
  -> Prog (Sig sig sigs sigl Id) a
fvar scope i = ctrace ("free " ++ show scope ++ " " ++ show i) $ do
  cs <- get @CStore
  ctrace (show cs) return ()
  i' <- lookupRenaming scope i
  applyC cs i'
 where
  applyC store n = case lookupC n store of
    Just (ConsC qn vs) -> ctrace "consc" $ do
      cons qn (map (applyC store) vs)
    Just (VarC j) -> ctrace "varc" $ applyC store j
    Just (LitC l) -> ctrace "litc" $ lit l
    _ -> ctrace "freec" $ injectA $ FFree n