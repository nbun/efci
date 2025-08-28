module Main where

import App (ToolOpts (..), defaultToolOpts, execute)
import Control.Concurrent
import Control.Monad (when)
import Curry.FlatCurry.Type
import Pipeline
import Test.HUnit.Base
import Test.Hspec

-- import Preload.CurryPrelude
import System.Directory (setCurrentDirectory)
import System.IO.Silently (capture)

main :: IO ()
main = do
    setCurrentDirectory "examples"
    res <- mapM (\(mod, expr, _, _) -> putStrLn (mod ++ " " ++ expr) >> capture (execute (defaultToolOpts{time = False}) (Left (mod, expr)))) progs
    let tests = zipWith (\(imp, expr, expctdRes, expctdOut) (output, result) -> (imp, expr, (expctdRes, expctdOut), (map withoutBindings result, output))) progs res
    hspec $ mapM_ (\(_, expr, expected, result) -> parallel $ it expr $ assertEqual "" expected result) tests

progs :: [(String, String, [Result], String)]
progs =
    [-- ND
      ("Prelude.curry", "0 ? 1 :: Int", [int 0, int 1], "")
    , ("Prelude.curry", "let x = 0 ? 1 in x + x :: Int", [int 0, int 2], "")
    , ("Prelude.curry", "let x = 0 ? 1 :: Int in (x + (0 ? 1)) + (x + (0 ? 1))", [int 0, int 1, int 1, int 2, int 2, int 3, int 3, int 4], "")
    , ("PermSort.curry", "sort [5,4,3,2,1::Int]", [toList [int 1, int 2, int 3, int 4, int 5]], "")

    -- Pattern matching & function application
    , ("Prelude.curry", "head [1::Int]", [int 1], "")
    , ("Prelude.curry", "x && x where x free", [false, true], "")
    , ("Peano.curry", "add O O", [RCons ("Peano", "O") []], "")
    , ("Peano.curry", "add (S O) O", [RCons ("Peano", "S") [RCons ("Peano", "O") []]], "")
    , ("Peano.curry", "p2i (add (S (S O)) (S (S O)))", [int 4], "")
    , ("Peano.curry", "p2i (Peano.pred (i2p 4))", [int 3], "")
    , ("Peano.curry", "p2i (mult (S (S O)) (S (S O)))", [int 4], "")
    , ("Peano.curry", "p2i (fac (i2p 4))", [RLit (Intc 24)], "")
    , ("Arith.curry", "fac 5", [RLit (Intc 120)], "")
    , ("Binary.curry", "run", [RCons ("Binary", "O") [RCons ("Binary", "O") [RCons ("Binary", "O") [RCons ("Binary", "I") [RCons ("Binary", "IHi") []]]]]], "")
    , ("Prelude.curry", "let f x = x + 1 in f 1 :: Int", [int 2], "")

    -- Laziness
    , ("Prelude.curry", "const (1 :: Int) (2 ? 3 :: Int)", [int 1], "")
    , ("Prelude.curry", "head [1 :: Int, 2 ? 3]", [int 1], "")
    , ("Prelude.curry", "head [(1 :: Int)..]", [int 1], "")

    -- Free variables
    , ("Peano.curry", "sub (S (S O)) (S O)", [RCons ("Peano", "S") [RCons ("Peano", "O") []]], "")
    , ("Uni.curry", "last [1..8::Int]", [int 8], "")
    , ("Uni.curry", "(sort intMerge [3,2,1] xs, xs) where xs free", [pair true (toList [int 1, int 2, int 3])], "")

    -- IO
    , ("Prelude.curry", "putStr \"Hello, World!\"", [unit], "Hello, World!")
    , ("Prelude.curry", "putChar 'x'", [unit], "x")
    , ("Prelude.curry", "putChar 'a' >> putChar 'b'", [unit], "ab")
    , ("Prelude.curry", "return 42 :: IO Int", [RLit (Intc 42)], "")
    , ("Prelude.curry", "return (2 * 2) :: IO Int", [int 4], "")
    , ("Prelude.curry", "return [(1 :: Int)..] >>= const (return True) :: IO Bool", [true], "")
    , ("Arith.Curry", "return loop >> return True :: IO Bool", [true], "")
    , ("Prelude.curry", "let io = putStrLn \"don't share me\" in io >> io", [unit], "don't share me\ndon't share me\n")

    -- Sharing and non-determinism
    , ("SharingSemantics.curry", "coin", [true, false], "")
    , ("SharingSemantics.curry", "coin ? coin", [true, false, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in x ? x", [true, false, true, false], "")
    , ("SharingSemantics.curry", "coin || False", [true, false], "")
    , ("SharingSemantics.curry", "coin || coin", [true, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in x || x", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in False || (x || x)", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in True || (x || x)", [true], "")
    , ("SharingSemantics.curry", "(coin ? coin) || True", [true, true, true, true], "")
    , ("SharingSemantics.curry", "(coin ? coin) || coin", [true, true, false, true, true, false], "")
    , ("SharingSemantics.curry", "coin || (coin ? coin)", [true, true, false, true, false], "")
    , ("SharingSemantics.curry", "(coin ? coin) || (coin ? coin)", [true, true, false, true, false, true, true, false, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in x || coin", [true, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in coin || x", [true, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in x || (x || coin)", [true, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in coin || (x || x)", [true, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in True || (x || x)", [true], "")
    , ("SharingSemantics.curry", "let x = coin in False || (x || x)", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in const x x", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in x || (const x x)", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in (const x x) || x", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in True || (const x x)", [true], "")
    , ("SharingSemantics.curry", "let x = (failed :: Bool) in const True x", [true], "")
    , ("SharingSemantics.curry", "head (coin : failed)", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in let y = x in y || y", [true, false], "")
    , ("SharingSemantics.curry", "let x = coin in const True (let y = x in y || y)", [true], "")
    , ("SharingSemantics.curry", "let x = coin in let y = coin in x || (y || (x || y))", [true, true, false], "")
    , ("SharingSemantics.curry", "let x = coin in x || (let y = coin in y || (x || y))", [true, true, false], "")
    , ("SharingSemantics.curry", "recList (True : False : [])", [toList [false, false], toList [false, true], toList [false, true]], "")
    , ("SharingSemantics.curry", "let x = coin in let y = coin in x : y : x : y : []", [toList [true, true, true, true], toList [true, false, true, false], toList [false, true, false, true], toList [false, false, false, false]], "")
    , ("SharingSemantics.curry", "dupRT (\\_ -> coin)", [pair true true, pair true false, pair false true, pair false false], "")
    , ("SharingSemantics.curry", "let x = coin in dupRT (\\_ -> x)", [pair true true, pair false false], "")
    , ("SharingSemantics.curry", "let x = coin in dupShare x", [pair true true, pair false false], "")
    , ("SharingSemantics.curry", "let x = (failed :: Bool) in dupRT (\\_ -> const True x)", [pair true true], "")
    , ("SharingSemantics.curry", "dupRT (\\_ -> (fst (coin, failed)))", [pair true true, pair true false, pair false true, pair false false], "")
    , ("SharingSemantics.curry", "dupShare (fst (coin, failed))", [pair true true, pair false false], "")
    , ("SharingSemantics.curry", "coini + coini", [int 0, int 1, int 1, int 2], "")
    , ("SharingSemantics.curry", "let x = coini in x + x", [int 0, int 2], "")
    , ("SharingSemantics.curry", "let x = coini in (x + coini) + (x + coini)", [int 0, int 1, int 1, int 2, int 2, int 3, int 3, int 4], "")
    , ("SharingSemantics.curry", "let y = (let x = coini in x + x) in y + y", [int 0, int 4], "")
    , ("SharingSemantics.curry", "let y = (let x = coini in x + x) in let z = coini in y + z", [int 0, int 1, int 2, int 3], "")
    , ("SharingSemantics.curry", "let x = 0 in x + (let y = (x + coini) in y + (let z = (y + coini) in z + 1))", [int 1, int 2, int 3, int 4], "")
    , ("SharingSemantics.curry", "let fxs = [coini] in (head fxs) + (head fxs)", [int 0, int 2], "")
    , ("SharingSemantics.curry", "let x = coin in [head (x : failed), head (x : failed)]", [toList [true, true], toList [false, false]], "")
    , ("SharingSemantics.curry", "let x = coin in [x, x]", [toList [true, true], toList [false, false]], "")
    , ("SharingSemantics.curry", "let x = coin in let y = coin in [x, y, x, y]", [toList [true, true, true, true], toList [true, false, true, false], toList [false, true, false, true], toList [false, false, false, false]], "")
    , ("SharingSemantics.curry", "let x = (True ? False) ? (True ? False) in (x,x)", [pair true true, pair false false, pair true true, pair false false], "")
    , ("SharingSemantics.curry", "let x = True ? (False ? True); y = True ? False in [x, y, x, y]", [toList [true, true, true, true], toList [true, false, true, false], toList [false, true, false, true], toList [false, false, false, false], toList [true, true, true, true], toList [true, false, true, false]], "")
    , ("SharingSemantics.curry", "let x = [True ? False] in (x,x)", [pair (toList [true]) (toList [true]), pair (toList [false]) (toList [false])], "")
    , ("SharingSemantics.curry", "let y = let x = coin in x || x in (y,y)", [pair true true, pair false false], "")
    , ("SharingSemantics.curry", "let ys = let xs = [coin, coin] in xs ++ xs in (ys,ys)", [pair (toList [true, true, true, true]) (toList [true, true, true, true]), pair (toList [true, false, true, false]) (toList [true, false, true, false]), pair (toList [false, true, false, true]) (toList [false, true, false, true]), pair (toList [false, false, false, false]) (toList [false, false, false, false])], "")
    , ("SharingSemantics.curry", "let ys = let xs = [coin] in xs ++ xs in ys ++ ys", [toList [true, true, true, true], toList [false, false, false, false]], "")
    , ("SharingSemantics.curry", "let ys = let xs = [coin] in xs ++ xs; x = coin; y = coin in x : y : ys", [toList [true, true, true, true], toList [true, true, false, false], toList [true, false, true, true], toList [true, false, false, false], toList [false, true, true, true], toList [false, true, false, false], toList [false, false, true, true], toList [false, false, false, false]], "")
    ]

int :: Integer -> Result
int x = RLit (Intc x)

unit, true, false, nil :: Result
unit = RCons ("Prelude", "()") []
true = RCons ("Prelude", "True") []
false = RCons ("Prelude", "False") []
nil = RCons ("Prelude", "[]") []

cons :: Result -> Result -> Result
cons h t = RCons ("Prelude", ":") [h, t]

toList :: [Result] -> Result
toList = foldr cons nil

pair :: Result -> Result -> Result
pair l r = RCons ("Prelude", "(,)") [l, r]
