module Main where

import           App                  ( execute, prepare, defaultToolOpts)
import           Curry.FlatCurry.Type
import           Pipeline
import           Test.Hspec
import Test.HUnit.Base
import Control.Concurrent
import Control.Monad (when)
-- import Preload.CurryPrelude
import System.Directory (setCurrentDirectory)

main :: IO ()
main = do
  setCurrentDirectory "examples"
  prelude <- prepare
  res <- mapM (\(mod, expr, expected) -> execute defaultToolOpts prelude mod expr) progs
  let tests = zipWith (\(imp, expr, expected) result -> (imp, expr, expected, result)) progs res
  hspec $ mapM_ (\(_, expr, expected, result) -> parallel $ it expr $ assertEqual "" expected result) tests

progs :: [(String, String, [Result])]
progs
  = [ ("Prelude.curry", "0 ? 1 :: Int", [RLit (Intc 0), RLit (Intc 1)])
    , ("Prelude.curry", "let x = 0 ? 1 in x + x :: Int", [RLit (Intc 0), RLit (Intc 2)])
    , ("Prelude.curry", "head [1::Int]", [RLit (Intc 1)])
    , ("Prelude.curry", "x && x where x free", [RCons ("Prelude", "False") [], RCons ("Prelude", "True") []])
    , ("Prelude.curry", "const (1 :: Int) (2 ? 3 :: Int)", [RLit (Intc 1)])
    , ("Prelude.curry", "head [1 :: Int, 2 ? 3]", [RLit (Intc 1)])
    , ("Prelude.curry", "let x = 0 ? 1 :: Int in x + x", [RLit (Intc 0), RLit (Intc 2)])
    , ("Prelude.curry", "let x = 0 ? 1 :: Int in (x + 0 ? 1) + (x + 0 ? 1)", [RLit (Intc 0),RLit (Intc 1),RLit (Intc 2),RLit (Intc 2),RLit (Intc 1),RLit (Intc 2),RLit (Intc 2)])
    , ("Prelude.curry", "let f x = x + 1 in f 1 :: Int", [RLit (Intc 2)])

    , ("Peano.curry", "add O O", [RCons ("Peano", "O") []])
    , ("Peano.curry", "add (S O) O", [RCons ("Peano", "S") [RCons ("Peano", "O") []]])
    , ("Peano.curry", "p2i (add (S (S O)) (S (S O)))", [RLit (Intc 4)])
    , ("Peano.curry", "p2i (Peano.pred (i2p 4))", [RLit (Intc 3)])
    , ("Peano.curry", "p2i (mult (S (S O)) (S (S O)))", [RLit (Intc 4)])
    , ("Peano.curry", "p2i (fac (i2p 4))", [RLit (Intc 24)])
   
    , ("Arith.curry", "fac 5", [RLit (Intc 120)])
   
    , ("Binary.curry", "run", [RCons ("Binary","O") [RCons ("Binary","O") [RCons ("Binary","O") [RCons ("Binary","I") [RCons ("Binary","IHi") []]]]]])

   
    , ("PermSort.curry", "sort [5,4,3,2,1::Int]", [RCons ("Prelude", ":") [RLit (Intc 1), RCons ("Prelude", ":") [RLit (Intc 2), RCons ("Prelude", ":") [RLit (Intc 3), RCons ("Prelude", ":") [RLit (Intc 4), RCons ("Prelude", ":") [RLit (Intc 5), RCons ("Prelude", "[]") []]]]]]])
    ]