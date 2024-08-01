import Criterion.Main
import Criterion.Types
import           App                  ( execute, prepare, defaultToolOpts, ToolOpts(..))
import           Curry.FlatCurry.Type
import           Pipeline
import Control.Monad (when)
import System.Directory (setCurrentDirectory)
import Debug.Trace (traceShowId)

main :: IO ()
main = do
  setCurrentDirectory "benchmarks"
  prelude <- prepare
--   res <- mapM (\(mod, expr, expected) -> execute defaultToolOpts prelude mod expr) progs
--   let tests = zipWith (\(imp, expr, expected) result -> (imp, expr, expected, result)) progs res
--   hspec $ mapM_ (\(_, expr, expected, result) -> parallel $ it expr $ assertEqual "" expected result) tests
  
  defaultMainWith (defaultConfig  { timeLimit = 1, csvFile = Just "bench.csv", reportFile = Just "report.html" }) [
       bgroup "Cod" [ bench "AddNum"   $ whnfIO (execute defaultToolOpts prelude "AddNum.curry" "isZero (addSomeNum1 200)")
                    , bench "AddNum5"   $ whnfIO (execute defaultToolOpts prelude "AddNum5.curry" "isZero (addSomeNum2 200)")
                      , bench "NRev"   $ whnfIO (execute defaultToolOpts prelude "NRev.curry" "isList (rev (natList nat16))")
                      , bench "PermSort"   $ whnfIO (execute defaultToolOpts prelude "PermSort.curry" "sortDescList 8")
                      , bench "PermSortPeano"   $ whnfIO (execute defaultToolOpts prelude "PermSortPeano.curry" "sortDescList (double four)")
                      , bench "PrimesHO"   $ whnfIO (execute defaultToolOpts prelude "PrimesHO.curry" "at primes 10")
                      , bench "Queens"   $ whnfIO (execute defaultToolOpts prelude "Queens.curry" "queens (S (S (S (S (S O)))))")
                      , bench "ReverseHO"   $ whnfIO (execute defaultToolOpts prelude "ReverseHO.curry" "revHO_256")
                      , bench "Select"   $ whnfIO (execute defaultToolOpts prelude "Select.curry" "select_50")
                      , bench "SortPrimes"   $ whnfIO (execute defaultToolOpts prelude "SortPrimes.curry" "psort [primes!!13, primes!!12, primes!!11]")
                      , bench "TakInt"   $ whnfIO (execute defaultToolOpts prelude "TakInt.curry" "tak 8 4 2") 
                      , bench "TakPeano"   $ whnfIO (execute defaultToolOpts prelude "TakPeano.curry" "tak n8 four two")
                      , bench "YesSAND"   $ whnfIO (execute defaultToolOpts prelude "YesSharingAcrossND.curry" "let p = at primes 10 in p ? p")
                      , bench "NoSAND"   $ whnfIO (execute defaultToolOpts prelude "NoSharingAcrossND.curry" "at primes 10 ? at primes 10")
       ]
      
       , bgroup "Prog" [ bench "AddNum"   $ whnfIO (execute noOptimize prelude "AddNum.curry" "isZero (addSomeNum1 200)")
                       , bench "AddNum5"   $ whnfIO (execute noOptimize prelude "AddNum5.curry" "isZero (addSomeNum2 200)")
                       , bench "PermSort"   $ whnfIO (execute noOptimize prelude "PermSort.curry" "sortDescList 8")
                       , bench "NRev"   $ whnfIO (execute noOptimize prelude "NRev.curry" "isList (rev (natList nat16))")
                       , bench "PermSortPeano"   $ whnfIO (execute noOptimize prelude "PermSortPeano.curry" "sortDescList (double four)")
                       , bench "PrimesHO"   $ whnfIO (execute noOptimize prelude "PrimesHO.curry" "at primes 10")
                       , bench "Queens"   $ whnfIO (execute noOptimize prelude "Queens.curry" "queens (S (S (S (S (S O)))))")
                       , bench "ReverseHO"   $ whnfIO (execute noOptimize prelude "ReverseHO.curry" "revHO_256")
                       , bench "Select"   $ whnfIO (execute noOptimize prelude "Select.curry" "select_50")
                       , bench "SortPrimes"   $ whnfIO (execute noOptimize prelude "SortPrimes.curry" "psort [primes!!13, primes!!12, primes!!11]")
                       , bench "TakInt"   $ whnfIO (execute noOptimize prelude "TakInt.curry" "tak 8 4 2")
                       , bench "TakPeano"   $ whnfIO (execute noOptimize prelude "TakPeano.curry" "tak n8 four two")
                       , bench "YesSAND"   $ whnfIO (execute noOptimize prelude "YesSharingAcrossND.curry" "let p = at primes 10 in p ? p")
                       , bench "NoSAND"   $ whnfIO (execute noOptimize prelude "NoSharingAcrossND.curry" "at primes 10 ? at primes 10")
       ]
       ]

noOptimize :: ToolOpts
noOptimize = defaultToolOpts { optimize = False }