{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

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

instance Functor ConsF where
  fmap _ (FCons qn args) = FCons qn args
  fmap f (FStrictCons qn args) = FStrictCons qn (map f args)
  fmap _ (FLit l) = FLit l
  fmap _ (FFree i) = FFree i
  {-# INLINE fmap #-}

data CaseScope a
  = Case a (Value () -> a)
  | Normalize a ((QName, [Ptr]) -> a)
  | External [a] ([Value ()] -> a)
  | Unify a a ((Value (), Value ()) -> a)

instance Functor CaseScope where
  fmap f (Case a k) = Case (f a) (f . k)
  fmap f (Normalize a k) = Normalize (f a) (f . k)
  fmap f (External as k) = External (map f as) (f . k)
  fmap f (Unify a1 a2 k) = Unify (f a1) (f a2) (f . k)
  {-# INLINE fmap #-}

data Mode
  = Strict
  | Lazy CaseType
  deriving (Eq, Show)

normalform
  :: ( ConsF :<: sig
     , Thunking a :<<<<: sigl
     , CaseScope :<: sigs
     , EffectMonad m sig sigs sigl Id
     )
  => m a
  -> m a
normalform p = ctrace "normalform" $
  do
    injectS (Normalize (fmap return p) (fmap return . f))
 where
  f (qn, ptrs) = do
    let args = map (normalform . force) ptrs
    injectA (FStrictCons qn args)
{-# INLINE normalform #-}

cons
  :: (EffectMonad m sig sigs sigl Id, Thunking a :<<<<: sigl, ConsF :<: sig)
  => QName
  -> [m a]
  -> m a
cons qn ps = do
  args <- mapM thunk ps
  ctrace ("cons " ++ show qn ++ " with " ++ show args) $
    injectA (FCons qn args)
{-# INLINE cons #-}

thunkedCons
  :: (EffectMonad m sig sigs sigl Id, Thunking a :<<<<: sigl, ConsF :<: sig)
  => QName
  -> [Ptr]
  -> m a
thunkedCons qn args = do
  ctrace ("thunkedCons " ++ show qn ++ " with " ++ show args) $
    injectA (FCons qn args)
{-# INLINE thunkedCons #-}

lit :: (EffectMonad m sig sigs sigl l, ConsF :<: sig) => Literal -> m a
lit l = injectA (FLit l)
{-# INLINE lit #-}

data CaseState

instance Identify CaseState where
  identify = "CaseState"

case'
  :: forall m sig sigs sigl a
   . (EffectMonad m sig sigs sigl Id, Let sig sigl a, CaseScope :<: sigs, ND :<: sig, ConstraintStore :<: sig, ConsF :<: sig)
  => Scope
  -> m a
  -> [(APattern (), m a)]
  -> m a
case' scope cp brs =
  ctrace "case" $
    injectS (Case (fmap return cp) (return . cnt))
 where
  cnt :: Value () -> m a
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
  deriving (Show)

instance Functor Value where
  fmap f (Cons qn args) = Cons qn (map (fmap f) args)
  fmap _ (HNF qn ptrs) = HNF qn ptrs
  fmap _ (Lit l) = Lit l
  fmap _ (Free i) = Free i
  fmap f (ValOther x) = ValOther (f x)
  {-# INLINE fmap #-}

newtype ValueL l a = ValueL {unValueL :: Value (l a)}
  deriving (Show)

instance Functor l => Functor (ValueL l) where
  fmap f (ValueL x) = ValueL (fmap (fmap f) x)
  {-# INLINE fmap #-}

runCons
  :: forall sig sigs sigl l a
   . (Functor sig, Functor sigs)
  => Prog (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l) a
  -> Prog (Sig sig sigs sigl (ValueL l)) (Value a)
runCons = ctrace "runCons" . unCC . fold point con
{-# INLINE runCons #-}

instance
  (EffectMonad m sig sigs sigl (ValueL l))
  => TermAlgebra (CC m) (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l)
  where
  con (A (Algebraic op)) = CC . (algCa # afwd) . fmap unCC $ op
   where
    algCa (FCons qn args) = return (HNF qn args)
    algCa (FStrictCons qn args) = sequence args <&> Cons qn
    algCa (FLit l) = return (Lit l)
    algCa (FFree i) = return (Free i)

    afwd = con . A . Algebraic
  con (S (Enter op)) = (algCs # sfwd) op
   where
    algCs (Case ce k) = CC $ do
      hnf <- unCC ce
      unCC (k (void hnf)) >>= lift'
    algCs (Normalize ce k) = CC $
      do
        hnf <- unCC ce
        case hnf of
          HNF qn args -> do
            hnf <- unCC (k (qn, args))
            case hnf of
              Cons qn args -> mapM lift' args <&> Cons qn
              Lit l -> return $ Lit l
              _ -> undefined
          Lit l -> return $ Lit l
          Free i -> return $ Free i
          Cons qn args -> mapM lift' args <&> Cons qn
          ValOther x -> unCC x
    algCs (External ps k) = CC $
      do
        hnfs <- mapM unCC ps
        hnf <- unCC $ k (map void hnfs)
        lift' hnf
    algCs (Unify e1 e2 k) = CC $
      do
        hnf1 <- unCC e1
        hnf2 <- unCC e2
        hnf <- unCC (k (void hnf1, void hnf2))
        lift' hnf

    lift' = lift . fmap unCC
    sfwd op = CC $ con $ S $ Enter $ fmap (fmap lift . unCC . fmap unCC) op
  con (L (Node op l st k)) = CC $ con $ L $ Node op (ValueL $ ValOther l) (st' st) k'
   where
    st' st2 c l' = lift2 (fmap (\x -> ValueL <$> unCC (st2 c x)) (unValueL l'))
    k' = lift . fmap (unCC . k) . unValueL
  {-# INLINE con #-}
  var = CC . gen'Error
   where
    gen'Error x = return (ValOther x)
  {-# INLINE var #-}

runConsC :: (EffectMonad m sig sigs sigl (ValueL l)) => Cod (CC m) a -> m (Value a)
runConsC = unCC . runCod var
{-# INLINE runConsC #-}

newtype CC m a = CC {unCC :: m (Value a)}
  deriving (Functor)

instance (Monad m) => Pointed (CC m) where
  point x = CC $ return (ValOther x)
  {-# INLINE point #-}

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

arithInt :: (ConsF :<: sig, CaseScope :<: sigs, TermMonad m (Sig sig sigs sigl l))
         => (Integer -> Integer -> Integer)
         -> m a 
         -> m a 
         -> m a 
arithInt op x y = injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Intc x), Lit (Intc y)] = lit (Intc (x `op` y))
{-# INLINE arithInt #-}

compInt :: ( ConsF :<: sig
           , Thunking v :<<<<: sigl
           , ConsF :<: sig
           , CaseScope :<: sigs
           , EffectMonad m sig sigs sigl Id)
        => (Integer -> Integer -> Bool)
        -> m v
        -> m v
        -> m v
compInt op x y = injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Intc x), Lit (Intc y)]
      | x `op` y = cons ("Prelude", "True") []
      | otherwise = cons ("Prelude", "False") []
{-# INLINE compInt #-}

compChar :: ( ConsF :<: sig
            , Thunking v :<<<<: sigl
            , ConsF :<: sig
            , CaseScope :<: sigs
            , EffectMonad m sig sigs sigl Id)
         => (Char -> Char -> Bool)
         -> m v
         -> m v
         -> m v
compChar op x y = 
  injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Charc x), Lit (Charc y)]
      | x `op` y = cons ("Prelude", "True") []
      | otherwise = cons ("Prelude", "False") []
{-# INLINE compChar #-}

err :: forall sig sigs sigl m v. ( CaseScope :<: sigs
       , Err :<: sig
       , Thunking v :<<<<: sigl
       , EffectMonad m sig sigs sigl Id)
    => m v
    -> m v
err p = do
  injectS (External [fmap return p] (return . f))
  where
    f :: [Value ()] -> m v
    f [hnf] = injectA (Err (val2str hnf))
{-# INLINE err #-}

val2str :: Show a => Value a -> [Char]
val2str (Cons ("Prelude", "[]") []) = ""
val2str (Cons ("Prelude", ":") [Lit (Charc c), xs]) = c:val2str xs
val2str hnf = error $ "hnf2str: " ++ show hnf

str2prog :: (Thunking a :<<<<: sigl, ConsF :<: sig, EffectMonad m sig sigs sigl Id)
         => String
         -> m a
str2prog [] = cons ("Prelude", "[]") []
str2prog (c:cs) = cons ("Prelude", ":") [lit (Charc c), str2prog cs]

-- free variables --

fvar
  :: ( ConsF :<: sig
     , Thunking a :<<<<: sigl
     , ConstraintStore :<: sig
     , Renaming :<: sig
     , EffectMonad m sig sigs sigl Id
     )
  => Scope
  -> VarIndex
  -> m a
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