import Criterion.Main
import Criterion.Types
import           App                  ( execute, loadProg, defaultToolOpts, ToolOpts(..))
import           Curry.FlatCurry.Annotated.Type
import           Pipeline
import Control.Monad (when)
import System.Directory (setCurrentDirectory)
import Debug.Trace (traceShowId)

main :: IO ()
main = do
  setCurrentDirectory "benchmarks"
  progs <- mapM (prepare defaultToolOpts) benchmarks
  defaultMainWith (defaultConfig  { timeLimit = 1, csvFile = Just "result/bench.csv", reportFile = Just "result/report.html" })
   [ bgroup "Cod" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute defaultToolOpts (Right (ps, expr)))) progs)
   , bgroup "Prog" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute noOptimize (Right (ps, expr)))) progs)
   ]

benchmarks :: [(String, String)]
benchmarks = [
  ("AddNum", "isZero (addSomeNum1 600)"),
  ("AddNum5", "isZero (addSomeNum2 600)"),
  ("NRev", "isList (rev (natList (mult nat16 (add four two))))"),
  ("PermSort", "sortDescList 8"),
  ("PermSortPeano", "sortDescList (double four)"),
  ("PrimesHO", "at primes 30"),
  ("Queens", "queens (S (S (S (S O))))"),
  ("ReverseHO", "isList (rev (natList (mult two nat256)))"),
  ("Select", "select [1..25]"),
  ("SortPrimes", "psort [primes!!10, primes!!9, primes!!8]"),
  ("TakInt", "tak 16 12 8"),
  ("TakPeano", "tak (add n8 four) n8 four"),
  ("YesSharingAcrossND", "let p = at primes 15 in p ? p"),
  ("NoSharingAcrossND", "at primes 15 ? at primes 15")
  ]

prepare :: ToolOpts -> (String, String) -> IO (String, [AProg TypeExpr], AFuncDecl TypeExpr)
prepare opts (mod, expr) = loadProg opts (mod ++ ".curry") expr >>= \(ps, expr) -> return (mod, ps, expr)

noOptimize :: ToolOpts
noOptimize = defaultToolOpts { optimize = False }