{-# LANGUAGE DataKinds #-}
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

module Effect.FlatCurry.Constructor (
    CaseScope (..),
    ConsF,
    Value (..),
    lit,
    str2prog,
    val2str,
    cons,
    arithInt,
    compInt,
    compChar,
    normalform,
    err,
    fvar,
    ValueL,
    CC,
    runCons,
    runConsC,
    runConsSmart,
    case',
    unit,
    true,
    false,
    ccons,
    arithFloat,
    compFloat,
    arithFloat2Float,
    arithFloat2Int,
    arithInt2Float,
    showCharLiteral,
    showIntLiteral,
    showFloatLiteral,
    readCharLiteral,
    readIntLiteral,
    readFloatLiteral,
    readStringLiteral,
    ordChar,
    chrChar
) where

import Control.Monad (void)
import Curry.FlatCurry.Annotated.Type (Literal (..))
import Curry.FlatCurry.Type (QName)
import Data.Functor ((<&>))
import Data.Maybe (mapMaybe)
import Effect.FlatCurry.Let
import Effect.General.Error (Err (..))
import Effect.General.Memoization
import Effect.General.ND (ND, choose, failed)
import Effect.General.State
import Free
import Signature
import Type
import Data.Char (ord, chr)
import GHC.Num (integerFromInt)

data ConsF a
    = FCons QName [Ptr]
    | FStrictCons QName [a]
    | FLit Literal
    | FFree Ptr
    deriving (Functor)

data CaseScope a
    = Case a (Value () -> a)
    | Normalize a ((QName, [Ptr]) -> a)
    | External [a] ([Value ()] -> a)
    | Unify a a ((Value (), Value ()) -> a)
    deriving (Functor)

normalform
    :: ( ConsF :<: sig
       , Thunking a :<<<<: sigl
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => m a
    -> m a
normalform p = logCall >> injectS (Normalize (fmap return p) (fmap return . f))
  where
    f (qn, ptrs) = do
        let args = map (normalform . force) ptrs
        injectA (FStrictCons qn args)
{-# INLINE normalform #-}

ccons
    :: (EffectCons m sig sigs sigl l, ConsF :<: sig)
    => QName
    -> m a
ccons qn = logCall >> injectA (FCons qn [])

cons
    :: (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, ConsF :<: sig)
    => QName
    -> Args m a
    -> m a
cons qn args =
    logCall >> do
        ptrs <- foldArgs (mapM store) return args
        injectA (FCons qn ptrs)
{-# INLINE cons #-}

lit :: (EffectCons m sig sigs sigl l, ConsF :<: sig) => Literal -> m a
lit l = logCall >> injectA (FLit l)
{-# INLINE lit #-}

case'
    :: forall m sig sigs sigl a
     . (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, Renaming :<: sig, CaseScope :<: sigs, ND :<: sig, ConstraintStore :<: sig, ConsF :<: sig)
    => m a
    -> [(AEPattern, m a)]
    -> m a
case' cp brs =
    logCall
        >> injectS (Case (fmap return cp) (return . cnt))
  where
    cnt :: Value () -> m a
    cnt val = case mapMaybe (match val) brs of
        [] -> failed
        [x] -> x
        xs -> choose xs

match :: (EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl, Renaming :<: sig, CaseScope :<: sigs, ND :<: sig, ConstraintStore :<: sig, ConsF :<: sig) => Value () -> (AEPattern, m a) -> Maybe (m a)
match (HNF qn args) (AEPattern pqn argPtrs, e)
    | pqn == qn =
        Just $ let' argPtrs (Thunks args) e
    | otherwise = Nothing
match (Lit l) (AELPattern lp, e)
    | l == lp = Just e
    | otherwise = Nothing
match (Free i) pat = Just $ do
    case pat of
        (AEPattern pqn argPtrs, e) -> do
            vs <- freshNames (length argPtrs)
            let fvs = Progs $ map fvar vs
            modify @CStore (addC i (ConsC pqn vs))
            let' argPtrs fvs e
        (AELPattern lp, e) -> do
            modify @CStore (addC i (LitC lp))
            e
match (ValOther ()) (AEPattern ("Prelude", "()") [], e) = Just e
match v ps =
    error $
        "Pattern match not implemented for " ++ show v ++ show (fst ps)

data Value a
    = Cons QName [Value a]
    | HNF QName [Ptr]
    | Lit Literal
    | Free Ptr
    | ValOther a
    deriving (Functor, Show)

instance Pointed Value where
    point = ValOther
    {-# INLINE point #-}

newtype ValueL l a = ValueL {unValueL :: Value (l a)}
    deriving (Functor, Show)

runCons
    :: (EffectCons m sig sigs sigl (ValueL l))
    => Prog (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l) a
    -> m (Value a)
runCons = unCC . fold point con
{-# INLINE runCons #-}

runConsSmart
    :: (EffectCons m sig sigs sigl (ValueL l))
    => SmartProg (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l) a
    -> m (Value a)
runConsSmart = unCC . smartFold point con
{-# INLINE runConsSmart #-}

instance LCarrier ValueL Value where
    lift (Cons qn args) = traverse lift args <&> Cons qn
    lift (HNF qn ptrs) = pure $ HNF qn ptrs
    lift (Lit l) = pure $ Lit l
    lift (Free i) = pure $ Free i
    lift (ValOther x) = x

    lift2 (Cons qn args) = traverse lift2 args <&> ValueL . Cons qn . map unValueL
    lift2 (HNF qn ptrs) = pure $ ValueL $ HNF qn ptrs
    lift2 (Lit l) = pure $ ValueL $ Lit l
    lift2 (Free i) = pure $ ValueL $ Free i
    lift2 (ValOther x) = x

instance OuterCarrier CC Value
instance DeriveForward 'Outer CC ValueL

algCa :: Monad m => ConsF (m (Value a)) -> m (Value a)
algCa (FCons qn args) = return (HNF qn args)
algCa (FStrictCons qn args) = sequence args <&> Cons qn
algCa (FLit l) = return (Lit l)
algCa (FFree i) = return (Free i)

algCs :: (Monad m, TermAlgebra m (Sig sig sigs sigl (cL l)),  LCarrier cL Value) => CaseScope (m (Value (m (Value a)))) -> m (Value a)
algCs (Case ce k) = do
            hnf <- ce
            k (void hnf) >>= lift
algCs (Normalize ce k) = do
    hnf <- ce
    case hnf of
        HNF qn args -> do
            hnf' <- k (qn, args)
            case hnf' of
                Cons qn' args' -> mapM lift args' <&> Cons qn'
                Lit l -> return $ Lit l
                Free i -> return $ Free i
                ValOther x -> x
                HNF _ _ -> error "Normalize: unexpected HNF"
        Lit l -> return $ Lit l
        Free i -> return $ Free i
        Cons qn args -> mapM lift args <&> Cons qn
        ValOther x -> x
algCs (External ps k) = do
    hnfs <- sequence ps
    hnf <- k (map void hnfs)
    lift hnf
algCs (Unify e1 e2 k) = do
    hnf1 <- e1
    hnf2 <- e2
    hnf <- k (void hnf1, void hnf2)
    lift hnf

instance
    (EffectMonad m sig sigs sigl (ValueL l))
    => TermAlgebra (CC m) (Sig (ConsF :+: sig) (CaseScope :+: sigs) sigl l)
    where
    con (A (Algebraic op)) = (wrap algCa # (afwd . Algebraic)) op
    con (S (Enter op)) = ((cc . algCs . fmap (unc . fmap unc)) # (sfwd . Enter)) op
    con (L op) = lfwd op
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

instance (Pointed m) => Pointed (CC m) where
    point x = CC $ point (ValOther x)
    {-# INLINE point #-}

unit, true, false :: (ConsF :<: sig, EffectCons m sig sigs sigl l) => m a
unit = ccons ("Prelude", "()")
true = ccons ("Prelude", "True")
false = ccons ("Prelude", "False")

externalError :: [Value ()] -> a
externalError vs = error $ "Malformed arguments to externally defined function: " ++ show vs

arithInt
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl l)
    => (Integer -> Integer -> Integer)
    -> m a
    -> m a
    -> m a
arithInt op p1 p2 = logCall >> injectS (External [fmap return p1, fmap return p2] (return . f))
  where
    f [Lit (Intc x), Lit (Intc y)] = lit (Intc (x `op` y))
    f vs = externalError vs
{-# INLINE arithInt #-}

compInt
    :: ( ConsF :<: sig
       , Thunking v :<<<<: sigl
       , ConsF :<: sig
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Integer -> Integer -> Bool)
    -> m v
    -> m v
    -> m v
compInt op x y = logCall >> injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Intc x1), Lit (Intc y1)]
        | x1 `op` y1 = true
        | otherwise = false
    f vs = externalError vs
{-# INLINE compInt #-}

compChar
    :: ( ConsF :<: sig
       , Thunking v :<<<<: sigl
       , ConsF :<: sig
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Char -> Char -> Bool)
    -> m v
    -> m v
    -> m v
compChar op x y =
    logCall >> injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Charc x1), Lit (Charc y1)]
        | x1 `op` y1 = true
        | otherwise = false
    f vs = externalError vs
{-# INLINE compChar #-}

ordChar :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id) => m a -> m a
ordChar x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Charc c)] = lit (Intc (integerFromInt $ ord c))
    f vs = externalError vs

chrChar :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id) => m a -> m a
chrChar x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Intc n)] = lit (Charc (chr (fromInteger n)))
    f vs = externalError vs


err
    :: forall sig sigs sigl m v
     . ( CaseScope :<: sigs
       , Err :<: sig
       , Thunking v :<<<<: sigl
       , EffectCons m sig sigs sigl Id
       )
    => m v
    -> m v
err p =
    logCall >> injectS (External [fmap return p] (return . f))
  where
    f :: [Value ()] -> m v
    f [hnf] = injectA (Err (val2str hnf))
    f vs = externalError vs
{-# INLINE err #-}

val2str :: (Show a) => Value a -> [Char]
val2str (Cons ("Prelude", "[]") []) = ""
val2str (Cons ("Prelude", ":") [Lit (Charc c), xs]) = c : val2str xs
val2str hnf = error $ "hnf2str: " ++ show hnf

str2prog
    :: (Thunking a :<<<<: sigl, ConsF :<: sig, EffectCons m sig sigs sigl Id)
    => String
    -> m a
str2prog cs = list2prog (map (lit . Charc) cs)

list2prog
    :: (Thunking a :<<<<: sigl, ConsF :<: sig, EffectCons m sig sigs sigl Id)
    => [m a]
    -> m a
list2prog [] = cons ("Prelude", "[]") (Progs [])
list2prog (x : xs) = cons ("Prelude", ":") (Progs [x, list2prog xs])

-- free variables --

fvar
    :: ( ConsF :<: sig
       , Thunking a :<<<<: sigl
       , ConstraintStore :<: sig
       , Renaming :<: sig
       , EffectCons m sig sigs sigl Id
       )
    => Ptr
    -> m a
fvar i =
    logCall >> do
        cs <- get @CStore
        applyC cs i
  where
    applyC cstore n = case lookupC n cstore of
        Just (ConsC qn vs) -> do
            cons qn (Progs $ map (applyC cstore) vs)
        Just (VarC j) -> applyC cstore j
        Just (LitC l) -> lit l
        _ -> injectA $ FFree n

--------

compFloat :: ( ConsF :<: sig
       , Thunking v :<<<<: sigl
       , ConsF :<: sig
       , CaseScope :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Double -> Double -> Bool)
    -> m v
    -> m v
    -> m v
compFloat op x y = logCall >> injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Floatc x1), Lit (Floatc y1)]
        | x1 `op` y1 = true
        | otherwise = false
    f vs = externalError vs
{-# INLINE compFloat #-}

arithFloat
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl l)
    => (Double -> Double -> Double)
    -> m a
    -> m a
    -> m a
arithFloat op x y = logCall >> injectS (External [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Floatc x1), Lit (Floatc y1)] = lit (Floatc (x1 `op` y1))
    f vs = externalError vs
{-# INLINE arithFloat #-}

arithFloat2Float
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl l)
    => (Double -> Double)
    -> m a
    -> m a
arithFloat2Float op x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Floatc x1)] = lit (Floatc (op x1))
    f vs = externalError vs
{-# INLINE arithFloat2Float #-}

arithFloat2Int
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl l)
    => (Double -> Integer)
    -> m a
    -> m a
arithFloat2Int op x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Floatc x1)] = lit (Intc (op x1))
    f vs = externalError vs
{-# INLINE arithFloat2Int #-}

arithInt2Float
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl l)
    => (Integer -> Double)
    -> m a
    -> m a
arithInt2Float op x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Intc x1)] = lit (Floatc (op x1))
    f vs = externalError vs
{-# INLINE arithInt2Float #-}


showCharLiteral
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => m a
    -> m a
showCharLiteral x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Charc c)] = str2prog (show c)
    f vs = externalError vs
{-# INLINE showCharLiteral #-}

showIntLiteral
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => m a
    -> m a
showIntLiteral x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Intc n)] = str2prog (show n)
    f vs = externalError vs
{-# INLINE showIntLiteral #-}

showFloatLiteral
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => m a
    -> m a
showFloatLiteral x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [Lit (Floatc n)] = str2prog (show n)
    f vs = externalError vs
{-# INLINE showFloatLiteral #-}

readCharLiteral
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => m a
    -> m a
readCharLiteral x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [r] = let res = read (val2str r)
            in list2prog $ map (\(c, rest) -> cons ("Prelude", "(,)") (Progs [lit (Charc c), str2prog rest])) res
    f vs = externalError vs
{-# INLINE readCharLiteral #-}

readIntLiteral
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => m a
    -> m a
readIntLiteral x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [r] = let res = read (val2str r)
            in list2prog $ map (\(i, rest) -> cons ("Prelude", "(,)") (Progs [lit (Intc i), str2prog rest])) res
    f vs = externalError vs
{-# INLINE readIntLiteral #-}

readFloatLiteral
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => m a
    -> m a
readFloatLiteral x = logCall >> injectS (External [fmap return x] (return . f))
  where
    f [r] = let res = read (val2str r)
            in list2prog $ map (\(fl, rest) -> cons ("Prelude", "(,)") (Progs [lit (Floatc fl), str2prog rest])) res
    f vs = externalError vs
{-# INLINE readFloatLiteral #-}

readStringLiteral
    :: (ConsF :<: sig, CaseScope :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<<<: sigl)
    => m a
    -> m a
readStringLiteral x = list2prog [cons ("Prelude", "(,)") (Progs [x, ccons ("Prelude", "[]")])]