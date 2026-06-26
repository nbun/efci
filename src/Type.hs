{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}

module Type (
    Ptr (..),
    analyzeVarIndex,
    AEFuncDecl (..),
    Module (..),
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
    fdclName,
    mkPtr,
) where

import Curry.FlatCurry.Annotated.Type
import qualified Curry.FlatCurry.Type as CFT (OpDecl (..))
import Data.Map (Map)
import qualified Data.Set as Set
import GHC.StableName
import GHC.Types.Unique (getKey)
import GHC.Types.Unique.Supply
import System.IO.Unsafe (unsafePerformIO)

findFDcl :: [AProg a] -> QName -> AFuncDecl a
findFDcl ps qn@(moduleName, _) = case res of
    Just fdecl -> fdecl
    Nothing -> error $ "Function declaration " ++ show qn ++ " not found"
  where
    res =
        foldr
            ( \(AProg name _ _ fdecls _) acc ->
                if name == moduleName
                    then findFuncDecl fdecls qn
                    else acc
            )
            Nothing
            ps

findFuncDecl :: [AFuncDecl a] -> QName -> Maybe (AFuncDecl a)
findFuncDecl fd qn = foldr (\fdecl acc -> if qn == funcName fdecl then Just fdecl else acc) Nothing fd
  where
    funcName (AFunc qn' _ _ _ _) = qn'

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
exprFuncs (ACase _ _ e alts) = exprFuncs e ++ concatMap (exprFuncs . (\(ABranch _ be) -> be)) alts
exprFuncs (AFree _ _ e) = exprFuncs e

declFuncs :: AFuncDecl a -> [QName]
declFuncs (AFunc _ _ _ _ e) = ruleFuncs e
  where
    ruleFuncs (ARule _ _ re) = exprFuncs re
    ruleFuncs (AExternal _ _) = []

reqFuncs :: forall a. [AProg a] -> AExpr a -> [AProg a]
reqFuncs ps e = reqFuncs' initial initial
  where
    initial = Set.fromList $ exprFuncs e

    reqFuncs' :: Set.Set QName -> Set.Set QName -> [AProg a]
    reqFuncs' acc new
        | Set.null new' = map (filterFuncs acc) ps
        | otherwise = reqFuncs' acc' new'
      where
        fset = Set.fromList $ concatMap (declFuncs . findFDcl ps) new
        new' = fset `Set.difference` acc
        acc' = acc `Set.union` fset

filterFuncs :: Set.Set QName -> AProg a -> AProg a
filterFuncs acc (AProg name imp tds fds ops) = AProg name imp tds fds' ops
  where
    fds' = filter (\(AFunc qn _ _ _ _) -> qn `elem` acc) fds

fdclBdy :: AFuncDecl a -> AExpr a
fdclBdy (AFunc _ _ _ _ (ARule _ _ a)) = a
fdclBdy (AFunc _ _ _ _ (AExternal _ _)) = error "fdclBdy: external function has no body"

withoutTDecls :: AProg a -> AProg a
withoutTDecls (AProg name imp _ fds ops) = AProg name imp [] fds ops

data Module a
    = Module
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

fdclName :: AEFuncDecl a -> QName
fdclName (AEFunc qn _ _ _ _) = qn

analyzeVarIndex :: String -> VarIndex -> String
analyzeVarIndex loc i = unsafePerformIO $ do
    sn <- makeStableName i
    return $ loc ++ " VarIndex " ++ show i ++ " with stable name hash " ++ show (hashStableName sn)

data Ptr = Ptr {-# NOUNPACK #-} Int String
    deriving (Eq, Ord, Show)

data Args m a = Progs [m a] | Thunks [Ptr]

single :: m a -> Args m a
single x = Progs [x]

foldArgs :: ([m a] -> b) -> ([Ptr] -> b) -> Args m a -> b
foldArgs f _ (Progs xs) = f xs
foldArgs _ g (Thunks xs) = g xs

freshPtr :: UniqSupply -> String -> (Ptr, UniqSupply)
freshPtr sup loc =
    let (!u, sup') = takeUniqFromSupply sup
        !i = fromIntegral (getKey u)
    in  (Ptr i loc, sup')
{-# INLINE freshPtr #-}

ptrKey :: Ptr -> VarIndex
ptrKey (Ptr i _) = i
{-# INLINE ptrKey #-}

mkPtr :: Int -> String -> Ptr
mkPtr = Ptr
{-# INLINE mkPtr #-}
