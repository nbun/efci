{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

{- A call-by-need interpreter using a heap to express sharing and support recursive bindings,
   and an environment to avoid substitution.  Extended to support free variables, narrowing,
   and non-determinism.  -}

module InterpFL where

import Control.Applicative (Alternative (..))
import Control.Monad
import Curry.FlatCurry.Annotated.Type
import qualified Data.IntMap as M
import Data.List
import qualified Data.Map as Map
import qualified Effect.FlatCurry.Constructor as FC
import Effect.FlatCurry.Function (Closure (..))
import qualified Effect.FlatCurry.Function as FCF

type Var = Int
type Constr = QName
type Prim = QName

data Pattern = CPat Constr [Var] | LPat Int
    deriving (Show, Eq)

data Exp
    = Var Var
    | Int Int
    | Abs Var Exp
    | App Exp Exp
    | Capp Constr [Exp]
    | Primapp Prim Exp Exp
    | Case Exp [(Pattern, Exp)]
    | Letrec [(Var, Exp)] Exp
    | Logic Var Exp
    deriving (Show, Eq)

-- Heap Pointers
type HPtr = Int

-- Values
data Value
    = VCapp Constr [HPtr]
    | VInt Int
    | VAbs Env Var Exp
    | VLogic HPtr
    deriving (Show, Eq)

data HEntry
    = HValue Value
    | HThunk Env Exp
    | HBlackhole
    deriving (Show)

type Env = M.IntMap HPtr

-- Heap: Free location supply plus bindings
data Heap = Heap {free :: [HPtr], bindings :: M.IntMap HEntry}
instance Show Heap where
    show (Heap free bindings) = show bindings
hfresh :: Heap -> (HPtr, Heap)
hfresh (Heap (v : vs) bindings) = (v, Heap vs bindings)
hempty :: Heap
hempty = Heap{free = [0 ..], bindings = M.empty}
hget :: Heap -> HPtr -> HEntry
hget (Heap free bindings) v = bindings M.! v
hset :: Heap -> (HPtr, HEntry) -> Heap
hset (Heap free bindings) (v, e) = Heap free (M.insert v e bindings)

{- Model answers as lists; inherits standard monad defns for lists.
type A a = [a]
alift = id
sols = id
-}

{- Model answers as forests; gives choice of dfs, bfs, etc. -}
type A a = Forest a
alift = liftF
dfsols :: A a -> [a]
dfsols = dfs
bfsols :: A a -> [a]
bfsols = bfs
sols = dfsols -- can change to whatever you want

-- Monad carries heap, and returns an answer structure
newtype M a = M (Heap -> A (a, Heap))
    deriving (Functor)

instance Applicative M where
    pure = return
    (<*>) = ap

instance Alternative M where
    empty = mzero
    (<|>) = mplus

instance MonadFail M where
    fail _ = mzero

instance Monad M where
    (M m1) >>= k =
        M
            ( \h -> do
                (a', h') <- m1 h
                let M m2 = k a' in m2 h'
            )
    return x = M (\h -> return (x, h))

instance MonadPlus M where
    mzero = M (\_ -> mzero)
    (M m1) `mplus` (M m2) = M (\h -> m1 h `mplus` m2 h)

fresh :: M HPtr
fresh = M (\h -> return (hfresh h))
store :: HPtr -> HEntry -> M ()
store p e = M (\h -> return ((), hset h (p, e)))
fetch :: HPtr -> M HEntry
fetch p = M (\h -> return (hget h p, h))
run :: M a -> A (a, Heap)
run (M m) = m hempty
lift :: M a -> M a
lift (M m) = M (\h -> alift (m h))

eval :: Env -> Exp -> M Value
eval env (Var x) =
    lift $
        do
            let p = env M.! x
            h <- fetch p
            case h of
                HThunk env' e' ->
                    do
                        store p HBlackhole
                        v' <- eval env' e'
                        store p (HValue v')
                        return v'
                HValue v -> return v
                HBlackhole -> mzero
eval env (Int i) = return (VInt i)
eval env (Abs x b) = return (VAbs env x b)
eval env (App e0 e1) =
    do
        VAbs env' x b <- eval env e0
        p1 <- fresh
        store p1 (HThunk env e1)
        let env'' = M.insert x p1 env'
        eval env'' b
eval env (Capp c es) =
    do
        ps <- mapM (const fresh) es
        zipWithM_ store ps (map (HThunk env) es)
        return (VCapp c ps)
eval env (Primapp p e1 e2) =
    do
        v1 <- eval env e1
        v2 <- eval env e2
        checkGround v1
        checkGround v2
        return (doPrimapp p v1 v2)
eval env (Case e pes) =
    do
        v <- eval env e
        case v of
            VCapp c0 ps ->
                do
                    let plookup [] = mzero
                        plookup ((CPat c xs, b) : pes)
                            | c == c0 = return (xs, b)
                            | otherwise = plookup pes
                    (xs, b) <- plookup pes
                    let env' = M.union (M.fromList (zip xs ps)) env
                    eval env' b
            VLogic p0 -> msum (map f pes)
              where
                f (CPat c xs, e') =
                    do
                        ps <- mapM (const allocLogic) xs
                        store p0 (HValue (VCapp c ps))
                        let env' = M.union (M.fromList (zip xs ps)) env
                        eval env' e'
            VInt i ->
                do
                    let plookup [] = mzero
                        plookup (((LPat j), b) : pes)
                            | i == j = return b
                            | otherwise = plookup pes
                    b <- plookup pes
                    eval env b
            _ -> error $ "unexpected value: " ++ show v
eval env (Letrec xes e) =
    do
        let (xs, es) = unzip xes
        ps <- mapM (const fresh) xes
        let env' = M.union (M.fromList (zip xs ps)) env
        zipWithM_ store ps (map (HThunk env') es)
        eval env' e
eval env (Logic x e) =
    do
        p <- allocLogic
        let env' = M.insert x p env
        eval env' e

allocLogic :: M HPtr
allocLogic = do p <- fresh; store p (HValue (VLogic p)); return p

checkGround :: Value -> M ()
checkGround (VLogic _) = mzero
checkGround _ = return ()

doPrimapp :: Prim -> Value -> Value -> Value
doPrimapp ("Prelude", "eqInt") (VInt i1) (VInt i2)
    | i1 == i2 = VCapp ("Prelude", "True") []
    | otherwise = VCapp ("Prelude", "False") []
doPrimapp ("Prelude", "plusInt") (VInt i) (VInt j) = VInt (i + j)
doPrimapp ("Prelude", "minusInt") (VInt i) (VInt j) = VInt (i - j)
doPrimapp ("Prelude", "timesInt") (VInt i) (VInt j) = VInt (i * j)
doPrimapp ("Prelude", "divInt") (VInt i) (VInt j) = VInt (div i j)
doPrimapp ("Prelude", "remInt") (VInt i) (VInt j) = VInt (rem i j)
doPrimapp ("Prelude", "modInt") (VInt i) (VInt j) = VInt (mod i j)
doPrimapp ("Prelude", "ltEqInt") (VInt i) (VInt j)
    | i <= j = VCapp ("Prelude", "True") []
    | otherwise = VCapp ("Prelude", "False") []
doPrimapp ("Prelude", "and") (VCapp ("Prelude", s1) []) (VCapp ("Prelude", s2) []) = case (s1, s2) of
    ("True", "True") -> VCapp ("Prelude", "True") []
    _ -> VCapp ("Prelude", "False") []
doPrimapp qn _ _ = error ("Unknown primitive: " ++ show qn)

interp :: Exp -> A (Value, Heap)
interp e = run (eval M.empty e)

interp' :: Exp -> [(Value, Heap)]
interp' = sols . interp

interp'' :: Exp -> [Value]
interp'' = nub . map fst . interp'

--------- Forest ------

newtype Forest a = Forest [Tree a]
    deriving (Functor, Show)
data Tree a = Leaf a | Fork (Forest a)
    deriving (Functor, Show)

instance Applicative Forest where
    pure = return
    (<*>) = ap

instance Monad Forest where
    m >>= k = forestjoin (forestmap k m)
    return a = Forest [Leaf a]

instance Alternative Forest where
    empty = mzero
    (<|>) = mplus

instance MonadPlus Forest where
    mzero = Forest []
    (Forest m1) `mplus` (Forest m2) = Forest (m1 ++ m2)

liftF :: Forest a -> Forest a
liftF f = Forest [Fork f]

forestjoin :: Forest (Forest a) -> Forest a
forestjoin (Forest ts) = Forest (concat (map join' ts))
  where
    join' :: Tree (Forest a) -> [Tree a]
    join' (Leaf (Forest ts)) = ts
    join' (Fork xff) = [Fork (forestjoin xff)]

treemap :: (a -> b) -> Tree a -> Tree b
treemap f (Leaf x) = Leaf (f x)
treemap f (Fork xf) = Fork (forestmap f xf)

forestmap :: (a -> b) -> Forest a -> Forest b
forestmap f (Forest ts) = Forest (map (treemap f) ts)

dfs :: Forest a -> [a]
dfs (Forest ts) = concat (map dfs' ts)
  where
    dfs' :: Tree a -> [a]
    dfs' (Leaf x) = [x]
    dfs' (Fork xf) = dfs xf

bfs :: Forest a -> [a]
bfs (Forest ts) = concat (bfs' ts)
  where
    bfs' :: [Tree a] -> [[a]]
    bfs' ts = combine (map levels ts)

    levels :: Tree a -> [[a]]
    levels (Leaf x) = [[x]]
    levels (Fork (Forest xf)) = [] : bfs' xf

    combine :: [[[a]]] -> [[a]]
    combine = foldr merge []

    merge :: [[a]] -> [[a]] -> [[a]]
    merge (x : xs) (y : ys) = (x ++ y) : (merge xs ys)
    merge xs [] = xs
    merge [] ys = ys

-- Translation to FlatCurry

translate :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> Exp
translate progs fdecl =
    let funs = concat [fs | AProg _ _ _ fs _ <- progs]
        funMap = Map.fromList $ (map (\fs@(AFunc qn _ _ _ _) -> (qn, fs))) funs
        expr = case fdecl of
            AFunc _ _ _ _ (ARule _ _ e) -> e
            _ -> error "External function not supported"
    in  translateExpr funMap expr

type FDeclMap = Map.Map QName (AFuncDecl TypeExpr)

transDef :: FDeclMap -> QName -> Exp
transDef funMap qn = case Map.lookup qn funMap of
    Just (AFunc _ _ _ _ (ARule _ params body)) ->
        foldr (\(v, _) acc -> Abs v acc) (translateExpr funMap body) params
    _ -> error ("Function not found: " ++ show qn)

translateExpr :: FDeclMap -> AExpr TypeExpr -> Exp
translateExpr funs e = case e of
    AVar _ v -> Var v
    ALit _ l -> case l of
        Intc i -> Int (fromInteger i)
        _ -> error "unsupported literal type"
    AComb _ _ (("Prelude", "apply"), _) [a1, a2] -> App (translateExpr funs a1) (translateExpr funs a2)
    AComb _ _ (("Prelude", "failed"), _) [] -> Logic (-42) (Case (Var (-42)) [])
    AComb _ ctype (qn, _) args -> case ctype of
        FuncCall ->
            if isPrimitive qn
                then case args of
                    [a1, a2] -> Primapp qn (translateExpr funs a1) (translateExpr funs a2)
                    _ -> foldl App (transDef funs qn) (map (translateExpr funs) args)
                else foldl App (transDef funs qn) (map (translateExpr funs) args)
        ConsCall -> Capp qn (map (translateExpr funs) args)
        FuncPartCall _ -> foldl App (transDef funs qn) (map (translateExpr funs) args)
        ConsPartCall missing ->
            let vars = [1 .. missing]
            in  foldr Abs (Capp qn (map (translateExpr funs) args ++ map Var vars)) vars
    ALet _ bs e' -> Letrec (map (\((v, _), expr) -> (v, translateExpr funs expr)) bs) (translateExpr funs e')
    AFree _ vs e' -> foldr (\(v, _) acc -> Logic v acc) (translateExpr funs e') vs
    AOr _ e1 e2 -> Logic (-42) (Case (Var (-42)) [(CPat ("Prelude", "Ldummy") [], translateExpr funs e1), (CPat ("Prelude", "Rdummy") [], translateExpr funs e2)])
    ACase _ _ e' brs -> Case (translateExpr funs e') (map (translateBranch funs) brs)
    ATyped _ e' _ -> translateExpr funs e'

translateBranch :: FDeclMap -> ABranchExpr TypeExpr -> (Pattern, Exp)
translateBranch funs (ABranch pat body) = (translatePat pat, translateExpr funs body)

translatePat :: APattern TypeExpr -> Pattern
translatePat (APattern _ (qn, _) vars) = CPat qn (map fst vars)
translatePat (ALPattern _ (Intc i)) = LPat (fromInteger i)
translatePat _ = error $ "unsupported pattern type"

isPrimitive :: QName -> Bool
isPrimitive (m, n) =
    m == "Prelude"
        && n
            `elem` [ "plusInt"
                   , "minusInt"
                   , "timesInt"
                   , "divInt"
                   , "modInt"
                   , "eqInt"
                   , "ltEqInt"
                   , "ltInt"
                   , "gtInt"
                   , "gtEqInt"
                   , "and"
                   , "or"
                   , "not"
                   , "apply"
                   , "$!"
                   , "bindIO"
                   , "returnIO"
                   , "prim_putChar"
                   , "failed"
                   , "remInt"
                   ]

runInterpFL :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> IO [FC.Value (Closure ())]
runInterpFL progs fdecl = do
    let expr = translate progs fdecl
    --   trace (show expr) (return ())
    let M action = do
            v <- eval M.empty expr
            -- trace (show v) (return ())
            nf v
    let results = sols (action hempty)
    return (map fst results)

nf :: Value -> M (FC.Value (Closure ()))
nf (VInt i) = return (FC.Lit (Intc (toInteger i)))
nf (VCapp c args) = do
    args' <-
        mapM
            ( \p -> do
                h <- fetch p
                case h of
                    HThunk env' e' -> do
                        store p HBlackhole
                        v' <- eval env' e'
                        store p (HValue v')
                        nf v'
                    HValue v' -> nf v'
                    HBlackhole -> mzero
            )
            args
    return (FC.NF c args')
nf (VAbs _ _ _) = return (FC.ValOther (Closure ("", "lambda") (FCF.FuncPartCall 1) []))
nf (VLogic _) = error "Unbound logic variable in result"
