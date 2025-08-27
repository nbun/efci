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
      ("Prelude.curry", "0 ? 1 :: Int", [RLit (Intc 0), RLit (Intc 1)], "")
    , ("Prelude.curry", "let x = 0 ? 1 in x + x :: Int", [RLit (Intc 0), RLit (Intc 2)], "")
    , ("Prelude.curry", "let x = 0 ? 1 :: Int in (x + (0 ? 1)) + (x + (0 ? 1))", [RLit (Intc 0), RLit (Intc 1), RLit (Intc 1), RLit (Intc 2), RLit (Intc 2), RLit (Intc 3), RLit (Intc 3), RLit (Intc 4)], "")
    , ("PermSort.curry", "sort [5,4,3,2,1::Int]", [RCons ("Prelude", ":") [RLit (Intc 1), RCons ("Prelude", ":") [RLit (Intc 2), RCons ("Prelude", ":") [RLit (Intc 3), RCons ("Prelude", ":") [RLit (Intc 4), RCons ("Prelude", ":") [RLit (Intc 5), RCons ("Prelude", "[]") []]]]]]], "")

    -- Pattern matching & function application
    , ("Prelude.curry", "head [1::Int]", [RLit (Intc 1)], "")
    , ("Prelude.curry", "x && x where x free", [false, true], "")
    , ("Peano.curry", "add O O", [RCons ("Peano", "O") []], "")
    , ("Peano.curry", "add (S O) O", [RCons ("Peano", "S") [RCons ("Peano", "O") []]], "")
    , ("Peano.curry", "p2i (add (S (S O)) (S (S O)))", [RLit (Intc 4)], "")
    , ("Peano.curry", "p2i (Peano.pred (i2p 4))", [RLit (Intc 3)], "")
    , ("Peano.curry", "p2i (mult (S (S O)) (S (S O)))", [RLit (Intc 4)], "")
    , ("Peano.curry", "p2i (fac (i2p 4))", [RLit (Intc 24)], "")
    , ("Arith.curry", "fac 5", [RLit (Intc 120)], "")
    , ("Binary.curry", "run", [RCons ("Binary", "O") [RCons ("Binary", "O") [RCons ("Binary", "O") [RCons ("Binary", "I") [RCons ("Binary", "IHi") []]]]]], "")
    , ("Prelude.curry", "let f x = x + 1 in f 1 :: Int", [RLit (Intc 2)], "")
    
    -- Laziness
    , ("Prelude.curry", "const (1 :: Int) (2 ? 3 :: Int)", [RLit (Intc 1)], "")
    , ("Prelude.curry", "head [1 :: Int, 2 ? 3]", [RLit (Intc 1)], "")   
    , ("Prelude.curry", "head [(1 :: Int)..]", [RLit (Intc 1)], "")   
    
    -- Free variables
    , ("Peano.curry", "sub (S (S O)) (S O)", [RCons ("Peano", "S") [RCons ("Peano", "O") []]], "")
    , ("Uni.curry", "last [1..8::Int]", [RLit (Intc 8)], "")
    , ("Uni.curry", "(sort intMerge [3,2,1] xs, xs) where xs free", [RCons ("Prelude", "(,)") [true, RCons ("Prelude", ":") [RLit (Intc 1), RCons ("Prelude", ":") [RLit (Intc 2), RCons ("Prelude", ":") [RLit (Intc 3), RCons ("Prelude", "[]") []]]]]], "")

    -- IO
    , ("Prelude.curry", "putStr \"Hello, World!\"", [unit], "Hello, World!")
    , ("Prelude.curry", "putChar 'x'", [unit], "x")
    , ("Prelude.curry", "putChar 'a' >> putChar 'b'", [unit], "ab")
    , ("Prelude.curry", "return 42 :: IO Int", [RLit (Intc 42)], "")
    , ("Prelude.curry", "return (2 * 2) :: IO Int", [RLit (Intc 4)], "")
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
    , ("SharingSemantics.curry", "recList (True : False : [])", [RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]], "")
    , ("SharingSemantics.curry", "let x = coin in let y = coin in x : y : x : y : []", [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]]], "")
    , ("SharingSemantics.curry", "dupRT (\\_ -> coin)", [RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [true, false], RCons ("Prelude", "(,)") [false, true], RCons ("Prelude", "(,)") [false, false]], "")
    , ("SharingSemantics.curry", "let x = coin in dupRT (\\_ -> x)", [RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [false, false]], "")
    , ("SharingSemantics.curry", "let x = coin in dupShare x", [RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [false, false]], "")
    , ("SharingSemantics.curry", "let x = (failed :: Bool) in dupRT (\\_ -> const True x)", [RCons ("Prelude", "(,)") [true, true]], "")
    , ("SharingSemantics.curry", "dupRT (\\_ -> (fst (coin, failed)))", [RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [true, false], RCons ("Prelude", "(,)") [false, true], RCons ("Prelude", "(,)") [false, false]], "")
    , ("SharingSemantics.curry", "dupShare (fst (coin, failed))", [RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [false, false]], "")
    , ("SharingSemantics.curry", "coini + coini", [RLit (Intc 0), RLit (Intc 1), RLit (Intc 1), RLit (Intc 2)], "")
    , ("SharingSemantics.curry", "let x = coini in x + x", [RLit (Intc 0), RLit (Intc 2)], "")
    , ("SharingSemantics.curry", "let x = coini in (x + coini) + (x + coini)", [RLit (Intc 0), RLit (Intc 1), RLit (Intc 1), RLit (Intc 2), RLit (Intc 2), RLit (Intc 3), RLit (Intc 3), RLit (Intc 4)], "")
    , ("SharingSemantics.curry", "let y = (let x = coini in x + x) in y + y", [RLit (Intc 0), RLit (Intc 4)], "")
    , ("SharingSemantics.curry", "let y = (let x = coini in x + x) in let z = coini in y + z", [RLit (Intc 0), RLit (Intc 1), RLit (Intc 2), RLit (Intc 3)], "")
    , ("SharingSemantics.curry", "let x = 0 in x + (let y = (x + coini) in y + (let z = (y + coini) in z + 1))", [RLit (Intc 1), RLit (Intc 2), RLit (Intc 3), RLit (Intc 4)], "")
    , ("SharingSemantics.curry", "let fxs = [coini] in (head fxs) + (head fxs)", [RLit (Intc 0), RLit (Intc 2)], "")
    , ("SharingSemantics.curry", "let x = coin in [head (x : failed), head (x : failed)]", [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]], "")
    , ("SharingSemantics.curry", "let x = coin in [x, x]", [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]], "")
    , ("SharingSemantics.curry", "let x = coin in let y = coin in [x, y, x, y]", [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]]], "")
    , ("SharingSemantics.curry", "let x = (True ? False) ? (True ? False) in (x,x)", [RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [false, false], RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [false, false]], "")
    , ("SharingSemantics.curry", "let x = True ? (False ? True); y = True ? False in [x, y, x, y]", [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]]], "")
    , ("SharingSemantics.curry", "let x = [True ? False] in (x,x)", [RCons ("Prelude", "(,)") [RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []], RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]], RCons ("Prelude", "(,)") [RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []], RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]], "")
    , ("SharingSemantics.curry", "let y = let x = coin in x || x in (y,y)", [RCons ("Prelude", "(,)") [true, true], RCons ("Prelude", "(,)") [false, false]], "")
    , ("SharingSemantics.curry", "let ys = let xs = [coin, coin] in xs ++ xs in (ys,ys)", [RCons ("Prelude", "(,)") [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]]], RCons ("Prelude", "(,)") [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]]], RCons ("Prelude", "(,)") [RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]]], RCons ("Prelude", "(,)") [RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]]]], "")
    , ("SharingSemantics.curry", "let ys = let xs = [coin] in xs ++ xs in ys ++ ys", [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]]], "")
    , ("SharingSemantics.curry", "let ys = let xs = [coin] in xs ++ xs; x = coin; y = coin in x : y : ys", [RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [true, RCons ("Prelude", ":") [true, RCons ("Prelude", "[]") []]]]], RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", ":") [false, RCons ("Prelude", "[]") []]]]]], "")
    ]

unit, true, false :: Result
unit = RCons ("Prelude", "()") []
true = RCons ("Prelude", "True") []
false = RCons ("Prelude", "False") []