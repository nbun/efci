{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Type (
    Ptr (..),
    analyzeVarIndex,
    AEFuncDecl (..),
    AEProg (..),
    fdclBody,
    Args (..),
    AEPattern (..),
    foldArgs,
    single,
    fdclBdy,
    reqFuncs,
    withoutTDecls,
    freshPtr,
    ptrKey,
) where

import Control.Monad.State.Strict
import Curry.FlatCurry.Annotated.Type
import Curry.FlatCurry.Type (
    QName,
    TypeDecl (..),
    TypeExpr (..),
    VarIndex,
    Visibility (..),
 )
import qualified Curry.FlatCurry.Type as CFT (OpDecl (..))
import qualified Data.IntMap.Strict as IntMap
import Data.List (insert, nub)
import Data.Map (Map)
import GHC.StableName
import GHC.Types.Unique (getKey)
import GHC.Types.Unique.Supply
import System.IO.Unsafe (unsafePerformIO)

findFDcl :: [AProg a] -> QName -> AFuncDecl a
findFDcl ps qn@(mod, _) = case res of
    Just fdecl -> fdecl
    Nothing -> error $ "Function declaration " ++ show qn ++ " not found"
  where
    res =
        foldr
            ( \(AProg name _ _ fdecls _) acc ->
                if name == mod
                    then findFuncDecl fdecls qn
                    else acc
            )
            Nothing
            ps

findFuncDecl :: [AFuncDecl a] -> QName -> Maybe (AFuncDecl a)
findFuncDecl fd qn = foldr (\fdecl acc -> if qn == funcName fdecl then Just fdecl else acc) Nothing fd
  where
    funcName (AFunc qn _ _ _ _) = qn

exprFuncs :: AExpr a -> [QName]
exprFuncs (AComb _ ct (f, _) args) =
    concatMap exprFuncs args ++ case ct of
        FuncCall -> [f]
        FuncPartCall _ -> [f]
        _ -> []
exprFuncs (AVar _ _) = []
exprFuncs (ALit _ _) = []
exprFuncs (ATyped _ e _) = exprFuncs e
exprFuncs (AOr _ e1 e2) = exprFuncs e1 ++ exprFuncs e2
exprFuncs (ALet _ bs e2) = concatMap (exprFuncs . snd) bs ++ exprFuncs e2
exprFuncs (ACase _ _ e alts) = exprFuncs e ++ concatMap (exprFuncs . (\(ABranch _ e) -> e)) alts
exprFuncs (AFree _ _ e) = exprFuncs e

declFuncs :: AFuncDecl a -> [QName]
declFuncs (AFunc _ _ _ _ e) = ruleFuncs e
  where
    ruleFuncs (ARule _ _ e) = exprFuncs e
    ruleFuncs (AExternal _ _) = []

reqFuncs :: (Show a) => [AProg a] -> AExpr a -> [AProg a]
reqFuncs ps e = reqFuncs' ps (nub $ exprFuncs e)
  where
    reqFuncs' ps acc
        | done = map (filterFuncs acc) ps
        | otherwise = reqFuncs' ps acc'
      where
        qns = concatMap (declFuncs . findFDcl ps) acc
        acc' = nub $ acc ++ qns
        done = length acc == length acc'

filterFuncs :: [QName] -> AProg a -> AProg a
filterFuncs acc (AProg name imp tds fds ops) = AProg name imp tds fds' ops
  where
    fds' = filter (\(AFunc qn _ _ _ _) -> qn `elem` acc) fds

fdclBdy :: AFuncDecl a -> AExpr a
fdclBdy (AFunc _ _ _ _ (ARule _ _ a)) = a

withoutTDecls :: AProg a -> AProg a
withoutTDecls (AProg name imp _ fds ops) = AProg name imp [] fds ops

data AEProg a
    = AEProg
        String
        [String]
        (Map QName TypeDecl)
        (Map QName (AEFuncDecl a))
        [CFT.OpDecl]
    deriving (Functor, Show)

data AEFuncDecl a = AEFunc QName Int Visibility TypeExpr a
    deriving (Functor, Show)

data AEBranchExpr a = AEBranch (APattern a) (AExpr a)
    deriving (Show)

data AEPattern
    = AEPattern QName [Ptr]
    | AELPattern Literal
    deriving (Show)

fdclBody :: AEFuncDecl a -> a
fdclBody (AEFunc _ _ _ _ a) = a

-- fdclVars :: AEFuncDecl a -> [VarIndex]
-- fdclVars (AEFunc _ _ _ _ (AERule vs _)) = vs

analyzeVarIndex :: String -> VarIndex -> String
analyzeVarIndex loc i = unsafePerformIO $ do
    sn <- makeStableName i
    return $ loc ++ " VarIndex " ++ show i ++ " with stable name hash " ++ show (hashStableName sn)

getHash :: a -> Int
getHash ptr = unsafePerformIO $ do
    sn <- makeStableName ptr
    return (hashStableName sn)

-- type Ptr = Int

data Ptr = Ptr {-# NOUNPACK #-} Int
    deriving (Eq, Ord, Show)

data Args m a = Progs [m a] | Thunks [Ptr]

single :: m a -> Args m a
single x = Progs [x]

foldArgs :: ([m a] -> b) -> ([Ptr] -> b) -> Args m a -> b
foldArgs f _ (Progs xs) = f xs
foldArgs _ g (Thunks xs) = g xs

freshPtr :: UniqSupply -> (Ptr, UniqSupply)
freshPtr sup =
    let (!u, sup') = takeUniqFromSupply sup
        !i = fromIntegral (getKey u)
     in (Ptr i, sup')
{-# INLINE freshPtr #-}

ptrKey :: Ptr -> VarIndex
ptrKey (Ptr i) = i
{-# INLINE ptrKey #-}

isTailRecursive :: QName -> AExpr a -> Bool
isTailRecursive qn e | funOccurs qn e = go e
  where
    go e = case e of
        AComb _ ct (f, _) args -> case ct of
            FuncCall -> f == qn && all (not . funOccurs qn) args
            _ -> False
        AVar _ _ -> True
        ALit _ _ -> True
        ATyped _ e' _ -> go e'
        AOr _ e1 e2 -> go e1 && go e2
        ALet _ bs e2 -> all (not . funOccurs qn . snd) bs && go e2
        ACase _ _ e alts -> not (funOccurs qn e) && all ((\(ABranch _ e') -> not (funOccurs qn e') || go e')) alts
        AFree _ _ e' -> go e'
isTailRecursive _ _ = False

funOccurs :: QName -> AExpr a -> Bool
funOccurs qn e =
    let rec = funOccurs qn
     in case e of
            AComb _ ct (f, _) args -> case ct of
                FuncCall -> f == qn || any rec args
                _ -> False
            AVar _ _ -> False
            ALit _ _ -> False
            ATyped _ e' _ -> rec e'
            AOr _ e1 e2 -> rec e1 || rec e2
            ALet _ bs e2 -> any (rec . snd) bs || rec e2
            ACase _ _ e alts -> rec e || any (rec . (\(ABranch _ e') -> e')) alts
            AFree _ _ e' -> rec e'

data VarInfo
    = NoInfo
    | VarInfo
        { count :: !Int
        , matched :: Bool
        }
    deriving (Show)

merge :: VarInfo -> VarInfo -> VarInfo
merge NoInfo m = m
merge m NoInfo = m
merge (VarInfo c1 m1) (VarInfo c2 m2) = VarInfo (max c1 c2) (m1 || m2)

-- propagate :: AExpr a -> VarIndex -> State InfoMap ()
-- propagate (AVar _ i) j | i == j = do
--   m <- get
--   case IntMap.lookup i m of
--     Just v -> do
--       IntMap.insert j (VarInfo c mtch) m
--     Nothing -> return ()

type InfoMap = IntMap.IntMap VarInfo

analyzeVars :: AExpr a -> State InfoMap ()
analyzeVars e = case e of
    AComb _ _ _ args -> mapM_ analyzeVars args
    AVar _ i -> incCount i
    ALit _ _ -> return ()
    ATyped _ e' _ -> analyzeVars e'
    AOr _ e1 e2 -> analyzeVars e1 >> analyzeVars e2
    ALet _ bs e2 -> do
        analyzeVars e2
        mapM_ (\(_, b) -> analyzeVars b) bs
    ACase _ _ e alts -> do
        analyzeVars e
        case e of
            AVar _ i -> setMatched i
            _ -> return ()
        s <- get
        let branchStates = snd $ mapM (\(ABranch _ b) -> runState (analyzeVars b) s) alts
        put $ foldr (\s acc -> IntMap.unionWith merge s acc) IntMap.empty branchStates
    AFree _ _ e' -> analyzeVars e'
  where
    incCount i = do
        m <- get
        let info = IntMap.findWithDefault NoInfo i m
            newInfo = case info of
                NoInfo -> VarInfo 1 False
                VarInfo cnt mtch -> VarInfo (cnt + 1) mtch
        put $ IntMap.insert i newInfo m
    setMatched i = do
        m <- get
        let info = IntMap.findWithDefault NoInfo i m
            newInfo = case info of
                NoInfo -> VarInfo 0 True
                VarInfo cnt _ -> VarInfo cnt True
        put $ IntMap.insert i newInfo m