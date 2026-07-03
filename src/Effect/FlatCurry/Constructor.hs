{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- | Term and pattern matching (TPM) effect

This module provides effects for term-related operations.
It includes:

* Creating literals and constructor-based values
* Pattern matching through @case@ expressions
* Lifting functions for implementing externally defined operations
* Semantic representations of values
-}
module Effect.FlatCurry.Constructor (
    Match (..),
    Term,
    Value (..),
    lit,
    str2prog,
    val2str,
    cons,
    arithInt,
    compInt,
    compChar,
    normalform,
    seq',
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
    chrChar,
) where

import Control.Monad (void, (>=>))
import Curry.FlatCurry.Annotated.Type (Literal (..))
import Curry.FlatCurry.Type (QName)
import Data.Char (chr, ord)
import Data.Functor ((<&>))
import Data.Maybe (mapMaybe)
import Effect.FlatCurry.Let
import Effect.General.Error (Err (..))
import Effect.General.Memoization
import Effect.General.ND (ND, choose, failed)
import Effect.General.State
import Forwarding
import Free
import GHC.Num (integerFromInt)
import Signature
import Type

{- | Effect for constructing terms

* 'TCons': Constructor application
* 'TLit': Literals
* 'TFree': Free variables
-}
data Term a
    = TCons QName [Ptr]
    | TLit Literal
    | TFree Ptr
    deriving (Functor)

{- | Normalization mode for term evaluation

* 'Seq': Evaluation to WHNF
* 'NormalForm': Evaluation to NF
-}
data Mode = Seq | NormalForm

{- | Effect for pattern matching operations

* 'Match': Operations that match on the 'Value' of one or multiple computations
* 'Normalize': Evaluation of computations according to a 'Mode'
-}
data Match a
    = Match [a] ([Value ()] -> a)
    | Normalize Mode a (Ptr -> a)
    deriving (Functor)

{- | Sequential evaluation operator

Forces evaluation of first argument to WHNF and returns second argument.
Used for forcing evaluation of arguments.
-}
seq'
    :: ( Term :<: sig
       , Thunking a :<<: sigl
       , Match :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => m a
    -> m a
    -> m a
seq' p q = logPrimCall >> injectS (Normalize Seq (fmap return p) (const $ return q))
{-# INLINE seq' #-}

{- | Normal form evaluation

Forces complete evaluation of a computation to normal form.
Used when full evaluation is required.
-}
normalform
    :: ( Term :<: sig
       , Thunking a :<<: sigl
       , Match :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => m a
    -> m a
normalform p = logPrimCall >> injectS (Normalize NormalForm (fmap return p) (return . normalform . force))
{-# INLINE normalform #-}

-- | Create a constructor term with no arguments from a qualified name
ccons
    :: (EffectCons m sig sigs sigl l, Term :<: sig)
    => QName
    -> m a
ccons qn = logPrimCall >> injectA (TCons qn [])

{- | Create a constructor application

Takes a qualified constructor name and 'Args' containing the constructor arguments,
returns the constructor application.
-}
cons
    :: (EffectCons m sig sigs sigl Id, Thunking a :<<: sigl, Term :<: sig)
    => QName
    -> Args m a
    -> m a
cons qn args =
    logPrimCall >> do
        ptrs <- foldArgs (mapM (store (fst qn ++ "." ++ snd qn ++ ".cons"))) return args
        injectA (TCons qn ptrs)
{-# INLINE cons #-}

-- | Create a literal value from a 'Literal'.
lit :: (EffectCons m sig sigs sigl l, Term :<: sig) => Literal -> m a
lit l = logPrimCall >> injectA (TLit l)
{-# INLINE lit #-}

{- | Pattern matching operation

Takes a computation to match against and a list of branches.
Non-deterministically returns *all* matching branches or a
non-deterministic failure if none matches.
-}
case'
    :: forall m sig sigs sigl a
     . (EffectCons m sig sigs sigl Id, Thunking a :<<: sigl, Renaming :<: sig, Match :<: sigs, ND :<: sig, ConstraintStore :<: sig, Term :<: sig)
    => m a
    -> [(AEPattern, m a)]
    -> m a
case' cp brs =
    logPrimCall
        >> injectS (Match [fmap return cp] (return . cnt))
  where
    cnt :: [Value ()] -> m a
    cnt [val] = case mapMaybe (match val) brs of
        [] -> failed
        [x] -> x
        xs -> choose xs -- needed for free variables
    cnt vs = error $ "case: unexpected values: " ++ show vs

-- | Helper function for implementing pattern matching
match :: (EffectCons m sig sigs sigl Id, Thunking a :<<: sigl, Renaming :<: sig, Match :<: sigs, ND :<: sig, ConstraintStore :<: sig, Term :<: sig) => Value () -> (AEPattern, m a) -> Maybe (m a)
match (HNF qn args) (AEPattern pqn argPtrs, e)
    | pqn == qn =
        Just $ let' argPtrs (Thunks args) e
    | otherwise = Nothing
match (NF qn args) (AEPattern pqn argPtrs, e)
    | pqn == qn =
        Just $ let' argPtrs (Progs $ map val2prog args) e
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
match v ps =
    error $
        "Pattern match not implemented for " ++ show v ++ show (fst ps)

{- | Convert a 'Value' to a effectful computation

Used when values need to be transformed into computations.
-}
val2prog :: (EffectCons m sig sigs sigl Id, Thunking a :<<: sigl, Term :<: sig, ConstraintStore :<: sig, Renaming :<: sig) => Value () -> m a
val2prog (NF qn args) = cons qn (Progs $ map val2prog args)
val2prog (HNF qn ptrs) = cons qn (Thunks ptrs)
val2prog (Lit l) = lit l
val2prog (Free i) = fvar i
val2prog (ValOther ()) = error "val2prog: ValOther () encountered"

{- | Value type for intermediate results

Represents different forms of values:

* 'NF': Value in normal form
* 'HNF': Head normal form with unevaluated arguments
* 'Lit': Literal value
* 'Free': Free variable
* 'ValOther': Semantic values of other effects
-}
data Value a
    = NF QName [Value a]
    | HNF QName [Ptr]
    | Lit Literal
    | Free Ptr
    | ValOther a
    deriving (Functor, Show, Foldable, Traversable)

instance Applicative Value where
    pure = ValOther
    NF qn args <*> v = NF qn (map (<*> v) args)
    HNF qn ptrs <*> _ = HNF qn ptrs
    Lit l <*> _ = Lit l
    Free i <*> _ = Free i
    ValOther f <*> x = fmap f x

instance Monad Value where
    NF qn args >>= f = NF qn (map (>>= f) args)
    HNF qn ptrs >>= _ = HNF qn ptrs
    Lit l >>= _ = Lit l
    Free i >>= _ = Free i
    ValOther x >>= f = f x

instance Pointed Value where
    point = ValOther
    {-# INLINE point #-}

{- | Value latent carrier

Combines a Value with a latent carrier @l@.
-}
newtype ValueL l a = ValueL {unValueL :: Value (l a)}
    deriving (Functor, Show)

{- | Handle TPM effect with tree-based interpretation

Folds a computation with TPM effects into a 'Value' result.
-}
runCons
    :: (EffectMonad m sig sigs sigl (ValueL l))
    => Prog (Sig (Term :+: sig) (Match :+: sigs) sigl l) a
    -> m (Value a)
runCons = unCC . fold point con
{-# INLINE runCons #-}

-- | Handle TPM effect with smart views
runConsSmart
    :: (EffectMonad m sig sigs sigl (ValueL l))
    => SmartProg (Sig (Term :+: sig) (Match :+: sigs) sigl l) a
    -> m (Value a)
runConsSmart = unCC . smartFold point con
{-# INLINE runConsSmart #-}

-- | Handle constructor effects with 'Codensity' representation
runConsC :: (EffectMonad m sig sigs sigl (ValueL l)) => Cod (CC m) a -> m (Value a)
runConsC = unCC . runCod var
{-# INLINE runConsC #-}

{- | TPM carrier newtype

Combines other carrier types with 'Value'.
-}
newtype CC m a = CC {unCC :: m (Value a)}
    deriving (Functor)

instance (Pointed m) => Pointed (CC m) where
    point x = CC $ point (ValOther x)
    {-# INLINE point #-}

instance LCarrier ValueL Value where
    concatM (NF qn args) = traverse concatM args <&> NF qn
    concatM (HNF qn ptrs) = pure $ HNF qn ptrs
    concatM (Lit l) = pure $ Lit l
    concatM (Free i) = pure $ Free i
    concatM (ValOther x) = x

instance Carrier CC Value
instance Forward 'Default CC ValueL

-- | Algebra for handling terms
algCa :: (Monad m) => Term (m (Value a)) -> m (Value a)
algCa (TCons qn args) = return (HNF qn args)
algCa (TLit l) = return (Lit l)
algCa (TFree i) = return (Free i)

-- | Algebra for handling matching and evaluation operations
algCs :: (TermMonad m (Sig sig sigs sigl (cL l)), LCarrier cL Value) => Match (m (Value (m (Value a)))) -> m (Value a)
algCs (Match ps k) = do
    hnfs <- sequence ps
    hnf <- k (map void hnfs)
    concatM hnf
algCs (Normalize mode ce k) = do
    hnf <- ce
    case (mode, hnf) of
        (NormalForm, HNF qn args) -> NF qn <$> mapM (k >=> concatM) args
        (Seq, _) -> k (error "") >>= concatM
        _ -> concatM hnf

-- | 'TermAlgebra' instance for handling the TPM effect
instance
    (EffectMonad m sig sigs sigl (ValueL l))
    => TermAlgebra (CC m) (Sig (Term :+: sig) (Match :+: sigs) sigl l)
    where
    con (A (Algebraic op)) = (wrap algCa # (afwd . Algebraic)) op
    con (S (Enter op)) = ((cc . algCs . fmap (unc . fmap unc)) # (sfwd . Enter)) op
    con (L op) = lfwd op
    {-# INLINE con #-}
    var = CC . gen'Error
      where
        gen'Error x = return (ValOther x)
    {-# INLINE var #-}

--- Lifting functions and effect-based representations of common constants ---

-- | Effect representation of common constants
unit, true, false :: (Term :<: sig, EffectCons m sig sigs sigl l) => m a
unit = ccons ("Prelude", "()")
true = ccons ("Prelude", "True")
false = ccons ("Prelude", "False")

{- | Error for unexpected arguments of external functions

Throws an error with a description of the supplied values.
-}
externalError :: [Value ()] -> a
externalError vs = error $ "Malformed arguments to externally defined function: " ++ show vs

{- | Integer arithmetic lifting function

Takes an arithmetic operator and two integer computations, returns a computation that applies the
operation.
-}
arithInt
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl l)
    => (Integer -> Integer -> Integer)
    -> m a
    -> m a
    -> m a
arithInt op p1 p2 = logPrimCall >> injectS (Match [fmap return p1, fmap return p2] (return . f))
  where
    f [Lit (Intc x), Lit (Intc y)] = lit (Intc (x `op` y))
    f vs = externalError vs
{-# INLINE arithInt #-}

{- | Integer comparison lifting function

Takes a comparison operator and two integer computations, returns a computation that produces
@True@ or @False@.
-}
compInt
    :: ( Term :<: sig
       , Thunking v :<<: sigl
       , Term :<: sig
       , Match :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Integer -> Integer -> Bool)
    -> m v
    -> m v
    -> m v
compInt op x y = logPrimCall >> injectS (Match [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Intc x1), Lit (Intc y1)]
        | x1 `op` y1 = true
        | otherwise = false
    f vs = externalError vs
{-# INLINE compInt #-}

{- | Character comparison lifting function

Takes a comparison operator and two character computations, returns a computation that produces
@True@ or @False@.
-}
compChar
    :: ( Term :<: sig
       , Thunking v :<<: sigl
       , Term :<: sig
       , Match :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Char -> Char -> Bool)
    -> m v
    -> m v
    -> m v
compChar op x y =
    logPrimCall >> injectS (Match [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Charc x1), Lit (Charc y1)]
        | x1 `op` y1 = true
        | otherwise = false
    f vs = externalError vs
{-# INLINE compChar #-}

{- | Convert a character to its integer value

Takes a computation that produces a character and returns a computation that produces the
integer representation.
-}
ordChar :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id) => m a -> m a
ordChar x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Charc c)] = lit (Intc (integerFromInt $ ord c))
    f vs = externalError vs

{- | Convert an integer to its corresponding character

Takes a computation that produces an integer and returns a computation that produces the
corresponding character value.
-}
chrChar :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id) => m a -> m a
chrChar x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Intc n)] = lit (Charc (chr (fromInteger n)))
    f vs = externalError vs

{- | Raise a runtime error

Takes a computation that evaluates to a 'String' and raises it as an error.
The error message is derived from the value using 'val2str'.
-}
err
    :: forall sig sigs sigl m v
     . ( Match :<: sigs
       , Err :<: sig
       , Thunking v :<<: sigl
       , EffectCons m sig sigs sigl Id
       )
    => m v
    -> m v
err p =
    logPrimCall >> injectS (Match [fmap return p] (return . f))
  where
    f :: [Value ()] -> m v
    f [hnf] = injectA (Err (val2str hnf))
    f vs = externalError vs
{-# INLINE err #-}

{- | Convert a 'Value' in normal form to a String representation

If the value is not fully evaluated, the function produces an error.
-}
val2str :: (Show a) => Value a -> String
val2str (NF ("Prelude", "[]") []) = ""
val2str (NF ("Prelude", ":") [Lit (Charc c), xs]) = c : val2str xs
val2str hnf = error $ "hnf2str: " ++ show hnf

{- | Convert a String to a computation

Creates a computation that represents a list of characters from the given string.
Each character is converted to a effect-based character literal.
-}
str2prog
    :: (Thunking a :<<: sigl, Term :<: sig, EffectCons m sig sigs sigl Id)
    => String
    -> m a
str2prog cs = list2prog (map (lit . Charc) cs)

-- | Convert a Haskell list into an effect-based list
list2prog
    :: (Thunking a :<<: sigl, Term :<: sig, EffectCons m sig sigs sigl Id)
    => [m a]
    -> m a
list2prog [] = cons ("Prelude", "[]") (Progs [])
list2prog (x : xs) = cons ("Prelude", ":") (Progs [x, list2prog xs])

{- | Floating-point comparison lifting function

Takes a comparison operator and two float computations, returns a computation
that produces @True@ or @False@.
-}
compFloat
    :: ( Term :<: sig
       , Thunking v :<<: sigl
       , Term :<: sig
       , Match :<: sigs
       , EffectCons m sig sigs sigl Id
       )
    => (Double -> Double -> Bool)
    -> m v
    -> m v
    -> m v
compFloat op x y = logPrimCall >> injectS (Match [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Floatc x1), Lit (Floatc y1)]
        | x1 `op` y1 = true
        | otherwise = false
    f vs = externalError vs
{-# INLINE compFloat #-}

{- | Floating-point arithmetic lifting function

Takes an arithmetic operator and two computations that produce floats,
returns a computation that applies the operation.
-}
arithFloat
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl l)
    => (Double -> Double -> Double)
    -> m a
    -> m a
    -> m a
arithFloat op x y = logPrimCall >> injectS (Match [fmap return x, fmap return y] (return . f))
  where
    f [Lit (Floatc x1), Lit (Floatc y1)] = lit (Floatc (x1 `op` y1))
    f vs = externalError vs
{-# INLINE arithFloat #-}

{- | Unary floating-point to floating-point lifting function

Takes a unary operator and a float computation, returns a computation
that applies the operation.
-}
arithFloat2Float
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl l)
    => (Double -> Double)
    -> m a
    -> m a
arithFloat2Float op x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Floatc x1)] = lit (Floatc (op x1))
    f vs = externalError vs
{-# INLINE arithFloat2Float #-}

{- | Floating-point to integer conversion lifting function

Takes a conversion operator and a float computation, returns a computation
that applies the operation.
-}
arithFloat2Int
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl l)
    => (Double -> Integer)
    -> m a
    -> m a
arithFloat2Int op x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Floatc x1)] = lit (Intc (op x1))
    f vs = externalError vs
{-# INLINE arithFloat2Int #-}

{- | Integer to floating-point conversion lifting function

Takes a conversion operator and an integer computation, returns a computation
that produces a @Float@.
-}
arithInt2Float
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl l)
    => (Integer -> Double)
    -> m a
    -> m a
arithInt2Float op x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Intc x1)] = lit (Floatc (op x1))
    f vs = externalError vs
{-# INLINE arithInt2Float #-}

{- | Show a character literal as a String

Takes a character computation and returns a computation that produces
its string representation.
-}
showCharLiteral
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => m a
    -> m a
showCharLiteral x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Charc c)] = str2prog (show c)
    f vs = externalError vs
{-# INLINE showCharLiteral #-}

{- | Show an integer literal as a String

Takes an integer computation and returns a computation that produces
its string representation.
-}
showIntLiteral
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => m a
    -> m a
showIntLiteral x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Intc n)] = str2prog (show n)
    f vs = externalError vs
{-# INLINE showIntLiteral #-}

{- | Show a floating-point literal as a String

Takes a float computation and returns a computation that produces
its string representation.
-}
showFloatLiteral
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => m a
    -> m a
showFloatLiteral x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [Lit (Floatc n)] = str2prog (show n)
    f vs = externalError vs
{-# INLINE showFloatLiteral #-}

{- | Read a character from a String

Takes a string computation and returns a computation that produces
all possible character readings.
Each element is a tuple of the parsed character and the remaining string.
-}
readCharLiteral
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => m a
    -> m a
readCharLiteral x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [r] =
        let res = read (val2str r)
        in  list2prog $ map (\(c, rest) -> cons ("Prelude", "(,)") (Progs [lit (Charc c), str2prog rest])) res
    f vs = externalError vs
{-# INLINE readCharLiteral #-}

{- | Read an integer from a String

Takes a string computation and returns a computation that produces
all possible integer readings.
Each element is a tuple of the parsed integer and the remaining string.
-}
readIntLiteral
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => m a
    -> m a
readIntLiteral x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [r] =
        let res = read (val2str r)
        in  list2prog $ map (\(i, rest) -> cons ("Prelude", "(,)") (Progs [lit (Intc i), str2prog rest])) res
    f vs = externalError vs
{-# INLINE readIntLiteral #-}

{- | Read a floating-point number from a String

Takes a string computation and returns a computation that produces
all possible float readings.
Each element is a tuple of the parsed float and the remaining string.
-}
readFloatLiteral
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => m a
    -> m a
readFloatLiteral x = logPrimCall >> injectS (Match [fmap return x] (return . f))
  where
    f [r] =
        let res = read (val2str r)
        in  list2prog $ map (\(fl, rest) -> cons ("Prelude", "(,)") (Progs [lit (Floatc fl), str2prog rest])) res
    f vs = externalError vs
{-# INLINE readFloatLiteral #-}

{- | Read an entire String

Takes a string computation and returns a computation that produces a tuple of the string and
an empty string.
-}
readStringLiteral
    :: (Term :<: sig, Match :<: sigs, EffectCons m sig sigs sigl Id, Thunking a :<<: sigl)
    => m a
    -> m a
readStringLiteral x = list2prog [cons ("Prelude", "(,)") (Progs [x, ccons ("Prelude", "[]")])]

--- Free variables ---

{- | Dereference a free variable

Looks up a free variable by its pointer in a 'ConstraintStore'
and produces a computation that represents the term as constrained by the
store. If the store contains no relevant constraints, the result is the
same free variable.
-}
fvar
    :: ( Term :<: sig
       , Thunking a :<<: sigl
       , ConstraintStore :<: sig
       , Renaming :<: sig
       , EffectCons m sig sigs sigl Id
       )
    => Ptr
    -> m a
fvar i =
    logPrimCall >> do
        cs <- get @CStore
        applyC cs i
  where
    applyC cstore n = case lookupC n cstore of
        Just (ConsC qn vs) -> do
            cons qn (Progs $ map (applyC cstore) vs)
        Just (VarC j) -> applyC cstore j
        Just (LitC l) -> lit l
        _ -> injectA $ TFree n