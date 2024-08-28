{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE RankNTypes #-}

module Monolith where

import Control.Monad (join)
import Control.Monad.State (StateT, evalStateT, get, put, MonadState)
import qualified Control.Monad.State.Class
import Curry.FlatCurry.Annotated.Type
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Effect.FlatCurry.Constructor (Value (..))
import Effect.FlatCurry.Function (Closure (..))
import Effect.General.Error (Error (..))
import Effect.General.Memoization (Ptr)
import Effect.General.State (Constraints, Scope, TraceInfo)
import Data.Functor (void)
import Debug.Trace (traceShowId, trace)
import Type (findFDcl)

-- IO ([TraceInfo], Error [(Constraints, Value (Closure a))])

-- data Result = Error String | Results [Result']
-- data Result' =

type Result = ([TraceInfo], Error [(Constraints, Value (Closure ()))])

data State = State
    { fargs :: Map.Map (Scope, Int) Ptr
    , memo :: IntMap.IntMap (Either (AExpr Scope) Result)
    , currentScope :: Scope
    , currentPtr :: Ptr
    , progs :: [AProg TypeExpr]
    }

initial :: [AProg TypeExpr] -> State
initial ps = State{progs = ps, fargs = Map.empty, memo = IntMap.empty, currentScope = 0, currentPtr = 0}

runMonolithic :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> IO Result
runMonolithic ps (AFunc _ _ _ _ (ARule _ _ e)) = evalStateT (execute (toScope (-1) e)) (initial ps)

toScope :: Functor f => Int -> f a -> f Scope
toScope i = trace ("toScope" ++ show i) fmap (const i)

updateScope :: (Functor f) => Scope -> f Scope -> f Scope
updateScope i = trace ("updateScope" ++ show i) fmap (\j -> if j == -1 then i else j)


execute :: AExpr Scope -> StateT State IO Result
execute expr = case expr of
    ALit _ l -> return ([], EOther [(Map.empty, Lit l)])
    AVar scope i -> do
        s <- get
        case Map.lookup (scope, i) (fargs s) of
            Nothing -> error $ "Variable not found " ++ show (scope, i)
            Just ptr -> case IntMap.lookup ptr (memo s) of
                Nothing -> error "Pointer not found"
                Just x -> case x of
                    Left e -> do
                        r <- execute e
                        put $ s{memo = IntMap.insert ptr (Right r) (memo s)}
                        return r
                    Right r -> return r
    ALet _ bs e -> do
        let (vs, es) = unzip bs
        s <- get
        let' (currentScope s) (map fst vs) es e
    AComb _ ct qn args -> case ct of
        FuncCall -> do
            s <- get
            let fd = findFDcl (progs s) (fst qn)
            if isExternal fd
                then do callExternal fd args
                else do
                    let scope = currentScope s
                    put $ s{currentScope = currentScope s + 1}
                    let' scope (fdclVars fd) args (fdclBody fd)
        ConsCall -> do
            ptrs <- mapM thunk args
            return ([], EOther [(Map.empty, HNF (fst qn) ptrs)])
        _ -> error "Comb type not supported"
    AOr _ e1 e2 -> do
        r1 <- execute e1
        r2 <- execute e2
        return $ combine r1 r2
    ACase _ _ e alts -> do
        r <- execute e
        case r of
            (_, Error s) -> return ([], Error s)
            (_, EOther xs) -> do
                s <- get
                let scope = currentScope s
                let xs' = join $ map (\x -> mapMaybe (match scope (snd x)) alts) xs
                xs'' <- sequence xs'
                return $ combineAll xs''
    ATyped _ e _ -> execute e

-- fcyExpr2ae
--     :: forall m
--      . (MonadState State m)
--     => AExpr TypeExpr
--     -> m (m Result)
-- fcyExpr2ae expr = do
--     case expr of
--         AVar _ i -> do
--             scope <- curScp
--             return $ lvar scope i fvar
--         ALit _ l -> return $ lit l
--         AComb _ FuncCall (("Prelude", "?"), _) [e1, e2] ->
--             liftM2 (?) (fcyExpr2ae e1) (fcyExpr2ae e2)
--         AComb _ FuncCall (("Prelude", "failed"), _) [] -> return failed
--         AComb _ FuncCall (("Prelude", "apply"), _) [fe, ee] ->
--             liftM2 apply' (fcyExpr2ae fe) (fcyExpr2ae ee)
--         AComb _ callType (qn, _) args -> do
--             args' <- mapM fcyExpr2ae args
--             case callType of
--                 FuncCall -> return $ fun qn (Left args')
--                 FuncPartCall i ->
--                     return $
--                         partial qn (Effect.FlatCurry.Function.FuncPartCall i) args'
--                 ConsCall -> return $ cons qn args'
--                 ConsPartCall i ->
--                     return $
--                         partial qn (Effect.FlatCurry.Function.ConsPartCall i) args'
--         -- _ -> error
--         -- \$ "FCY2AE.fcyExpr2ae: comb type not supported for " ++ show qn
--         ALet _ bs e -> do
--             let ((vs, _), es) = first unzip (unzip bs)
--             es' <- mapM fcyExpr2ae es
--             e' <- fcyExpr2ae e
--             scope <- curScp
--             return $ let' scope (zip vs es') e'
--         AFree _ bs e -> fcyExpr2ae e
--         AOr _ e1 e2 -> do
--             liftM2 (?) (fcyExpr2ae e1) (fcyExpr2ae e2)
--         ACase _ ct e brs -> do
--             e' <- fcyExpr2ae e
--             brs' <-
--                 mapM
--                     (\(ABranch pat e') -> fmap (patf pat,) (fcyExpr2ae e'))
--                     brs
--             scope <- curScp
--             return $ case' scope e' brs'
--           where
--             patf (APattern _ (qn, _) vars) = APattern () (qn, ()) (map void vars)
--             patf (ALPattern _ l) = ALPattern () l
--         ATyped _ e t -> fcyExpr2ae e -- type annotations not required
--   where
--     curScp = do
--         s <- get
--         return $ currentScope s
--     lvar scope i fvar = do
--         s <- get
--         case Map.lookup (scope, i) (fargs s) of
--             Nothing -> error $ "Variable not found " ++ show (scope, i)
--             Just ptr -> force ptr
--     force ptr = do
--         s <- get
--         case IntMap.lookup ptr (memo s) of
--             Nothing -> error "Pointer not found"
--             Just x -> case x of
--                 Left e -> do
--                     r <- execute e
--                     put $ s{memo = IntMap.insert ptr (Right r) (memo s)}
--                     return r
--                 Right r -> return r
--     lit l = return ([], EOther [(Map.empty, Lit l)])

callExternal :: AFuncDecl a -> [AExpr Scope] -> StateT State IO Result
callExternal fdecl args = do
    s <- get
    let scope = currentScope s
        args' = map (updateScope scope) args
    case (externalName fdecl, args') of
      ("Prelude.plusInt", [px, py]) -> arithInt (f2l (+)) px py
      ("Prelude.minusInt", [px, py]) -> arithInt (f2l (-)) px py
      ("Prelude.timesInt", [px, py]) -> arithInt (f2l (*)) px py
      ("Prelude.divInt", [px, py]) -> arithInt (f2l div) px py
      ("Prelude.modInt", [px, py]) -> arithInt (f2l mod) px py
      -- ("Prelude.eqInt", [px, py]) -> compInt (==) px py
      -- ("Prelude.ltEqInt", [px, py]) -> compInt (<=) px py
      -- ("Prelude.eqChar", [px, py]) -> compChar (==) px py
  where
    arithInt f px py = do
        (t1, x) <- execute px
        (t2, y) <- execute py
        return (t1 ++ t2, apply f x y)

f2l :: (Integer -> Integer -> Integer) -> Literal -> Literal -> Literal
f2l f ((Intc x)) ((Intc y)) = Intc (f x y)

apply :: (Literal -> Literal -> Literal)
       -> Error [(Constraints, Value (Closure ()))]
       -> Error [(Constraints, Value (Closure ()))]
       -> Error [(Constraints, Value (Closure ()))]
apply _ (Error e) _ = Error e
apply _ _ (Error e) = Error e
apply f (EOther xs) (EOther ys) = EOther [apply' x y | x <- xs, y <- ys ]
  where
    apply' :: (Constraints, Value (Closure ())) -> (Constraints, Value (Closure ())) -> (Constraints, Value (Closure ()))
    apply' (cs1, Lit l1) (cs2, Lit l2) = (Map.union cs1 cs2, Lit (f l1 l2))


combine :: Result -> Result -> Result
combine (t1, Error e) (t2, Error _) = (t1 ++ t2, Error e)
combine (t1, EOther _) (t2, Error e) = (t1 ++ t2, Error e)
combine (t1, EOther xs) (t2, EOther ys) = (t1 ++ t2, EOther (xs ++ ys))

combineAll :: [Result] -> Result
combineAll = foldr combine ([], EOther [])

let' :: Scope -> [VarIndex] -> [AExpr Scope] -> AExpr Scope -> StateT State IO Result
let' scope vs es e = do
    let es' = map (updateScope scope) es
    ptrs <- mapM thunk es' 
    letThunked scope vs ptrs (updateScope scope e)

letThunked :: Scope -> [VarIndex] -> [Ptr]-> AExpr Scope -> StateT State IO Result
letThunked scope vs ptrs e = do
    s <- get
    let fargs' = Map.union (Map.fromList (traceShowId $ zip (map (scope,) vs) ptrs)) (fargs s)
    put $ s{fargs = fargs'}
    execute e

thunk :: (Control.Monad.State.Class.MonadState State m) => AExpr Scope -> m Ptr
thunk e = do
    s <- get
    let ptr = currentPtr s
    put $ s{memo = IntMap.insert ptr (Left e) (memo s), currentPtr = ptr + 1}
    return ptr

match :: (Show a) => Scope -> Value a -> ABranchExpr Scope -> Maybe (StateT State IO Result)
match scope (HNF qn args) (ABranch (APattern _ (pqn, _) argVars) e)
    | pqn == qn = Just $ do
        letThunked scope (map fst argVars) args e
    | otherwise = Nothing
match scope (Lit l) (ABranch (ALPattern _ lp) e)
    | l == lp = Just (execute e)
    | otherwise = Nothing
-- match (Free i) pat = Just $ do
--     case pat of
--         (APattern _ (pqn, _) argVars, e) -> do
--             vs <- freshNames (length argVars)
--             let fvs = map (fvar scope) vs
--             modify @CStore (addC i (ConsC pqn (map (scope,) vs)))
--             let' scope (zip (map fst argVars) fvs) e
--         (ALPattern _ lp, e) -> do
--             modify @CStore (addC i (LitC lp))
--             e
match scope v ps =
    error $
        "Pattern match not implemented for " ++ show v ++ show ps



fdclBody :: AFuncDecl a -> AExpr Scope
fdclBody (AFunc _ _ _ _ (ARule _ _ a)) = toScope (-1) a

fdclVars :: AFuncDecl a -> [VarIndex]
fdclVars (AFunc _ _ _ _ (ARule _ vs _)) = map fst vs

isExternal :: AFuncDecl a -> Bool
isExternal (AFunc _ _ _ _ r) = case r of
    ARule _ _ _ -> False
    AExternal _ _ -> True

externalName :: AFuncDecl a -> String
externalName (AFunc _ _ _ _ r) = case r of
    AExternal _ s -> s
    _ -> undefined