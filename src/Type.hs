{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}

module Type where

import Curry.FlatCurry.Type (
  QName,
  TypeDecl (..),
  TypeExpr (..),
  VarIndex,
  Visibility (..),
 )
import qualified Curry.FlatCurry.Type as CFT (OpDecl (..))
import Data.Map (Map)
import Curry.FlatCurry.Annotated.Type
import Data.List (nub)
import System.IO.Unsafe (unsafePerformIO)
import GHC.StableName
import GHC.HeapView (getClosureData)
import GHC.Types.Unique.Supply
import GHC.Types.Unique (getKey)

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
exprFuncs (AComb _ ct (f, _) args) = concatMap exprFuncs args ++ case ct of
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
  where ruleFuncs (ARule _ _ e) = exprFuncs e
        ruleFuncs (AExternal _ _) = []

reqFuncs :: Show a => [AProg a] -> AExpr a -> [AProg a]
reqFuncs ps e = reqFuncs' ps (nub $ exprFuncs e)
  where reqFuncs' ps acc | done = map (filterFuncs acc) ps
                         | otherwise = reqFuncs' ps acc'
          where
            qns = concatMap (declFuncs . findFDcl ps) acc
            acc' = nub $ acc ++ qns
            done = length acc == length acc'

filterFuncs :: [QName] -> AProg a -> AProg a
filterFuncs acc (AProg name imp tds fds ops) = AProg name imp tds fds' ops
  where fds' = filter (\(AFunc qn _ _ _ _) -> qn `elem` acc) fds

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

data AEFuncDecl a = AEFunc QName Int Visibility TypeExpr (AERule a)
  deriving (Functor, Show)

fdclBody :: AEFuncDecl a -> a
fdclBody (AEFunc _ _ _ _ (AERule _ a)) = a

fdclVars :: AEFuncDecl a -> [VarIndex]
fdclVars (AEFunc _ _ _ _ (AERule vs _)) = vs

data AERule a
  = AERule [VarIndex] a
  | AEExternal String
  deriving (Functor, Show)

analyzeVarIndex :: String -> VarIndex -> String
analyzeVarIndex loc i = unsafePerformIO $ do
  sn <- makeStableName i
  cl <- getClosureData i
  return $ loc ++ " VarIndex " ++ show i ++ " with stable name hash " ++ show (hashStableName sn)  ++ " and closure type " ++ show cl ++ "\n"

getHash :: a -> Int
getHash ptr = unsafePerformIO $ do
  sn <- makeStableName ptr
  return (hashStableName sn)

freshVarIndex :: UniqSupply -> (VarIndex, UniqSupply)
freshVarIndex sup = let (!u, sup') = takeUniqFromSupply sup
                        !i = fromIntegral (getKey u)
                    in (i, sup')