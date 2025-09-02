import Criterion.Main
import Criterion.Types
import           App                  ( execute, loadProg, defaultToolOpts, ToolOpts(..), Mode (..))
import           Curry.FlatCurry.Annotated.Type
import           Pipeline
import Control.Monad (when)
import System.Directory (setCurrentDirectory)
import Debug.Trace (traceShowId)
import System.Process (callCommand)
import Control.Concurrent (setNumCapabilities)

main :: IO ()
main = do
  setNumCapabilities 16
  setCurrentDirectory "benchmarks"
  progs <- mapM (prepare defaultToolOpts) benchmarks
  -- mapM_ preparePakcs benchmarks
  defaultMainWith (defaultConfig  { timeLimit = 1, csvFile = Just "result/bench.csv", reportFile = Just "result/report.html" })
    [ --bgroup "Mono" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Monolithic) (Right (ps, expr)))) progs)
    --  bgroup "Cod" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Codensity) (Right (ps, expr)))) progs)
      bgroup "Smart" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Smart) (Right (ps, expr)))) progs)
    -- , bgroup "Prog" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Tree) (Right (ps, expr)))) progs)
    -- , bgroup "pakcs" (map (\(mod, expr) -> bench mod $ whnfIO (callCommand $ "./" ++ mod )) benchmarks)
    -- , bgroup "pakcs-eval" (map (\(mod, expr) -> bench mod $ whnfIO (runPakcs (mod, expr))) benchmarks)
   ]
  -- mapM_ deletePakcs benchmarks

escapePar :: String -> String
escapePar = concatMap (\c -> if c == '(' then "\\(" else if c == ')' then "\\)" else [c])

preparePakcs :: (String, String) -> IO ()
preparePakcs (mod, expr) = callCommand $ "/home/nbu/.local/pakcs-3.7.1/bin/pakcs --nocypm :l " ++ mod ++ ".curry :save " ++ escapePar expr ++ " :q"

runPakcs :: (String, String) -> IO ()
runPakcs (mod, expr) = callCommand $ "/home/nbu/.local/pakcs-3.7.1/bin/pakcs --nocypm :l " ++ mod ++ ".curry :eval " ++ escapePar expr ++ " :q"


deletePakcs :: (String, String) -> IO ()
deletePakcs (mod, expr) = callCommand $ "rm " ++ mod

benchmarks :: [(String, String)]
benchmarks = [
  ("AddNum", "isZero (addSomeNum1 750)"),
  ("AddNum5", "isZero (addSomeNum2 800)"),
  ("NRev", "isList (rev (natList (mult nat16 (add four four))))"),
  ("PermSort", "sortDescList 9"),
  ("PermSortPeano", "sortDescList (double four)"),
  ("PrimesHO", "at primes 35"),
  ("Queens", "queens (S (S (S (S (S  O)))))"),
  ("ReverseHO", "isList (rev (natList (mult four nat256)))"),
  ("Select", "select [1..50]"),
  ("SortPrimes", "psort [primes!!10, primes!!9, primes!!8]"),
  ("TakInt", "tak 16 14 8"),
  ("TakPeano", "tak (add n8 four) n8 four"),
  ("YesSharingAcrossND", "let p = at primes 25 in p ? p"),
  ("NoSharingAcrossND", "at primes 25 ? at primes 25")
  ]

prepare :: ToolOpts -> (String, String) -> IO (String, [AProg TypeExpr], AFuncDecl TypeExpr)
prepare opts (mod, expr) = loadProg opts (mod ++ ".curry") expr >>= \(Right (ps, expr)) -> return (mod, ps, expr)

setMode :: Mode -> ToolOpts
setMode m = defaultToolOpts { mode = m, time = False}
