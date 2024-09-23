{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}

module Monolith where

import Control.Monad (join, liftM2)
import Control.Monad.State (StateT, evalStateT, get, put, MonadState)
import qualified Control.Monad.State.Class
import Curry.FlatCurry.Annotated.Type hiding (Cons)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Effect.FlatCurry.Constructor (Value (..))
import Effect.FlatCurry.Function (Closure (..), decArgs)
import Effect.General.Error (Error (..))
import Effect.General.Memoization (Ptr)
import Effect.General.State (Constraints, Scope, TraceInfo)
import Data.Functor (void)
import Debug.Trace (traceShowId, trace)
import Type (findFDcl)
import Data.Bifunctor (first)
import qualified Effect.FlatCurry.Function

-- IO ([TraceInfo], Error [(Constraints, Value (Closure a))])

-- data Result = Error String | Results [Result']
-- data Result' =

type Result = ([TraceInfo], Error [(Constraints, Value (Closure ()))])

data State = State
    { fargs :: Map.Map (Scope, Int) Ptr
    , memo :: IntMap.IntMap (Either (StateT State IO Result) Result)
    , currentScope :: Scope
    , currentPtr :: Ptr
    , progs :: [AProg TypeExpr]
    }

-- initial :: [AProg TypeExpr] -> State m
-- initial ps = State{progs = ps, fargs = Map.empty, memo = IntMap.empty, currentScope = 0, currentPtr = 0}

runMonolithic :: [AProg TypeExpr] -> AFuncDecl TypeExpr -> IO Result
runMonolithic ps (AFunc _ _ _ _ (ARule _ _ e)) = evalStateT (normalform $ join $ fcyExpr2ae e) initial
  where initial = State{progs = ps, fargs = Map.empty, memo = IntMap.empty, currentScope = 0, currentPtr = 0}





fcyExpr2ae
    :: forall m
     . (m ~ StateT State IO)
    => AExpr TypeExpr
    -> m (m Result)
fcyExpr2ae expr = let return = Prelude.return . trace (show (void expr)) in do
    case expr of
        AVar _ i -> do
            scope <- curScp
            return $ lvar scope i
        ALit _ l -> return $ lit l
        AComb _ FuncCall (("Prelude", "?"), _) [e1, e2] ->
            liftM2 (?) (fcyExpr2ae e1) (fcyExpr2ae e2)
        AComb _ FuncCall (("Prelude", "failed"), _) [] -> return failed
        AComb _ FuncCall (("Prelude", "apply"), _) [fe, ee] ->
            liftM2 apply' (fcyExpr2ae fe) (fcyExpr2ae ee)
        AComb _ callType (qn, _) args -> do
            args' <- mapM fcyExpr2ae args
            case callType of
                FuncCall -> return $ fun qn (Left args')
                FuncPartCall i ->
                    return $
                        partial qn (Effect.FlatCurry.Function.FuncPartCall i) args'
                ConsCall -> return $ cons qn args'
                ConsPartCall i ->
                    return $
                        partial qn (Effect.FlatCurry.Function.ConsPartCall i) args'
        -- -- _ -> error
        -- -- \$ "FCY2AE.fcyExpr2ae: comb type not supported for " ++ show qn
        ALet _ bs e -> do
            let ((vs, _), es) = first unzip (unzip bs)
            es' <- mapM fcyExpr2ae es
            e' <- fcyExpr2ae e
            scope <- curScp
            return $ let' scope vs es' e'
        -- AFree _ bs e -> fcyExpr2ae e
        AOr _ e1 e2 -> do
            liftM2 (?) (fcyExpr2ae e1) (fcyExpr2ae e2)
        ACase _ ct e brs -> do
            e' <- fcyExpr2ae e
            brs' <-
                mapM
                    (\(ABranch pat e') -> fmap (patf pat,) (fcyExpr2ae e'))
                    brs
            scope <- curScp
            return $ case' scope e' brs'
          where
            patf (APattern _ (qn, _) vars) = APattern () (qn, ()) (map void vars)
            patf (ALPattern _ l) = ALPattern () l
        ATyped _ e _ -> fcyExpr2ae e -- type annotations not required
        _ -> error $ "FCY2AE.fcyExpr2ae: expression type not supported: " ++ show expr
  where
    fvar = undefined

apply' :: forall m. (m ~ StateT State IO) => m Result -> m Result -> m Result
apply' mf mx = do
    ptr <- thunk mx
    f <- mf
    case f of
      (_, EOther [(_, ValOther (Closure qn ct ptrs))]) ->
            let ptrs' = ptrs ++ [ptr]
            in case ct of
                Effect.FlatCurry.Function.FuncPartCall 1 -> do
                    fun qn (Right ptrs')
                Effect.FlatCurry.Function.ConsPartCall 1 -> return ([], EOther [(Map.empty, HNF qn ptrs')])
                _ -> return ([], EOther [(Map.empty, ValOther (Closure qn (decArgs ct) ptrs'))])

partial :: forall m. (m ~ StateT State IO) => QName -> Effect.FlatCurry.Function.CombType -> [m Result] -> m Result
partial qn ct args = do
    ptrs <- mapM thunk args
    return ([], EOther [(Map.empty, ValOther (Closure qn ct ptrs))])


curScp :: forall m. (m ~ StateT State IO) => m Scope
curScp = fmap currentScope get

newScp :: forall m. (m ~ StateT State IO) => m Scope
newScp = do
    s <- get
    put $ s{currentScope = currentScope s + 1}
    -- if currentScope s == 10 then undefined else return ()
    return $ currentScope s + 1

lvar :: forall m. (m ~ StateT State IO) => Scope -> Int -> m Result
lvar scope i = do
    s <- get
    case Map.lookup (scope, i) (fargs s) of
        Nothing -> error $ "Variable not found " ++ show (scope, i)
        Just ptr -> force ptr

force :: forall m. (m ~ StateT State IO) => Ptr -> m Result
force ptr = trace ("force " ++ show ptr) $ do
    s <- get
    case IntMap.lookup ptr (memo s) of
        Nothing -> error "Pointer not found"
        Just x -> case x of
            Left e -> do
                r <- e
                s <- get
                put $ s{memo = IntMap.insert ptr (Right r) (memo s)}
                return r
            Right r -> trace ("memo " ++ show r) return r

lit :: forall m. (m ~ StateT State IO) => Literal -> m Result
lit l = return ([], EOther [(Map.empty, Lit l)])

failed :: forall m. (m ~ StateT State IO) => m Result
failed = return ([], EOther [])

(?) :: forall m. (m ~ StateT State IO) => m Result -> m Result -> m Result
(?) = liftM2 combine

let' :: forall m. (m ~ StateT State IO) => Scope -> [VarIndex] -> [m Result] -> m Result -> m Result
let' scope vs es e = do
    ptrs <- mapM thunk es
    trace ("let' " ++ show ptrs) $ return ()
    letThunked scope vs ptrs e

letThunked :: forall m. (m ~ StateT State IO) => Scope -> [VarIndex] -> [Ptr]-> m Result -> m Result
letThunked scope vs ptrs e = do
    s <- get
    let fargs' = Map.union (Map.fromList (traceShowId $ zip (map (scope,) vs) ptrs)) (fargs s)
    put $ s{fargs = traceShowId fargs'}
    e

thunk :: forall m. (m ~ StateT State IO) => m Result -> m Ptr
thunk e = do
    s <- get
    let ptr = currentPtr s
    put $ s{memo = IntMap.insert ptr (Left e) (memo s), currentPtr = ptr + 1}
    trace ("thunk " ++ show ptr) $ return ptr

fun :: forall m. (m ~ StateT State IO) => QName -> Either [m Result] [Ptr] -> m Result
fun qn args = do
    scope <- newScp
    s <- get
    let fd = findFDcl (progs s) qn
    case isExternal fd of
        True -> do
            let args' = either id (map force) args
            callExternal fd args'
        False -> case args of
            Left es -> do
                e <- fcyExpr2ae (fdclBody fd)
                let' scope (fdclVars fd) es e
            Right ptrs -> do
                e <- fcyExpr2ae (fdclBody fd)
                letThunked scope (fdclVars fd) ptrs e

callExternal :: forall m a. (m ~ StateT State IO) => AFuncDecl a -> [m Result] -> m Result
callExternal fdecl args = do
    case (externalName fdecl, args) of
        ("Prelude.plusInt", [px, py]) -> arithInt (f2l (+)) px py
        ("Prelude.minusInt", [px, py]) -> arithInt (f2l (-)) px py
        ("Prelude.timesInt", [px, py]) -> arithInt (f2l (*)) px py
        ("Prelude.divInt", [px, py]) -> arithInt (f2l div) px py
        ("Prelude.modInt", [px, py]) -> arithInt (f2l mod) px py
        ("Prelude.eqInt", [px, py]) -> compInt (==) px py
        ("Prelude.ltEqInt", [px, py]) -> compInt (<=) px py
    --   ("Prelude.eqChar", [px, py]) -> compChar (==) px py
        _ -> error $ "External function not implemented: " ++ externalName fdecl
    where
    arithInt f px py = do
        (t1, x) <- px
        (t2, y) <- py
        return (t1 ++ t2, apply f x y)

    compInt f px py = do
        (t1, x) <- px
        (t2, y) <- py
        let f' (Intc x) (Intc y) = if f x y then HNF ("Prelude", "True") [] else HNF ("Prelude", "False") []
        return (t1 ++ t2, applyCons f' x y)

cons :: forall m. (m ~ StateT State IO) => QName -> [m Result] -> m Result
cons qn args = do
    ptrs <- mapM thunk args
    return ([], EOther [(Map.empty, HNF qn ptrs)])

case' :: forall m. (m ~ StateT State IO) => Scope -> m Result -> [(APattern (), m Result)] -> m Result
case' scope e brs = do
    r <- e
    case r of
        (ts, Error e) -> return (ts, Error e)
        (ts, EOther rs) -> do
        --   res <- sequence $ concat [mapMaybe (match scope r) brs | r <- rs]
        --   return (combineAll res)
            case mapMaybe (match scope (head rs)) brs of
                [] -> return ([], EOther [])
                [r] -> r


match :: forall m. (m ~ StateT State IO) => Scope -> (Constraints, Value (Closure ())) -> (APattern (), m Result) -> Maybe (m Result)
match scope (_, HNF qn args) (APattern _ (pqn, _) argVars, e)
    | pqn == qn = Just $ do
        letThunked scope (map fst argVars) args e
    | otherwise = Nothing
match scope (_, Lit l) (ALPattern _ lp, e)
    | l == lp = Just e
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
        "Pattern match not implemented for " ++ show v

normalform :: forall m. (m ~ StateT State IO) => m Result -> m Result
normalform p = do
    r <- p
    case r of
        (ts, Error e) -> return (ts, Error e)
        (ts, EOther xs) -> do
            rs <- mapM (normalform' ts) xs
            return (combineAll rs)

normalform' :: forall m. (m ~ StateT State IO) => [TraceInfo] -> (Constraints, Value (Closure ())) -> m Result
normalform' ti (cs, HNF qn ptrs) = do  --(cs, Cons qn xs)
    xs <- mapM (normalform . force) ptrs
    let (tis, es) = unzip xs
        ti' = ti ++ concat tis
        e = combineE es
    case e of
        Error e' -> return (ti', Error e')
        EOther es' -> return (ti', EOther [(cs, Cons qn (map snd es'))])
normalform' ti x = return (ti, EOther [x])

combineE :: [Error [a]] -> Error [a]
combineE [] = EOther []
combineE (Error e:_) = Error e
combineE (EOther e:es) = case combineE es of
    Error e' -> Error e'
    EOther e' -> EOther (e ++ e')
    

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

applyCons :: (Literal -> Literal -> Value (Closure ()))
       -> Error [(Constraints, Value (Closure ()))]
       -> Error [(Constraints, Value (Closure ()))]
       -> Error [(Constraints, Value (Closure ()))]
applyCons _ (Error e) _ = Error e
applyCons _ _ (Error e) = Error e
applyCons f (EOther xs) (EOther ys) = EOther [apply' x y | x <- xs, y <- ys ]
  where
    apply' :: (Constraints, Value (Closure ())) -> (Constraints, Value (Closure ())) -> (Constraints, Value (Closure ()))
    apply' (cs1, Lit l1) (cs2, Lit l2) = (Map.union cs1 cs2, f l1 l2)

combine :: Result -> Result -> Result
combine (t1, Error e) (t2, Error _) = (t1 ++ t2, Error e)
combine (t1, EOther _) (t2, Error e) = (t1 ++ t2, Error e)
combine (t1, EOther xs) (t2, EOther ys) = (t1 ++ t2, EOther (xs ++ ys))

combineAll :: [Result] -> Result
combineAll = foldr combine ([], EOther [])


fdclBody :: AFuncDecl a -> AExpr a
fdclBody (AFunc _ _ _ _ (ARule _ _ a)) = a

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