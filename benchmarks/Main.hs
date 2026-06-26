import Criterion.Main
import Criterion.Types
import App ( execute, loadProg, defaultToolOpts, ToolOpts(..), Mode (..))
import Curry.FlatCurry.Annotated.Type
import Pipeline
import Control.Monad (when)
import System.Directory (setCurrentDirectory)
import Debug.Trace (traceShowId)
import System.Process (callCommand)
import Control.Concurrent (setNumCapabilities)

-- Paths to binaries of PAKCS or KiCS2, modify as needed
binPAKCS, binKICS :: String
binPAKCS = "/home/nbu/.local/pakcs-3.7.0/bin/pakcs"
binKICS  = "/home/nbu/.local/kics2-3.5.0-x86_64-linux/bin/kics2"

-- Main benchmarking function
-- When including external compilers, uncomment the respective lines for
-- pre-compiling the benchmark programs.
main :: IO ()
main = do
  setNumCapabilities 16
  setCurrentDirectory "benchmarks"
  progs <- mapM (prepare defaultToolOpts) benchmarks
  -- mapM_ preparePakcs benchmarks
  -- mapM_ prepareKics benchmarks
  defaultMainWith (defaultConfig  { timeLimit = 1, csvFile = Just "result/bench.csv", reportFile = Just "result/report.html" })
    [ 
      bgroup "Mono" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Monolithic) (Right (ps, expr)))) progs),
      bgroup "Cod" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Codensity) (Right (ps, expr)))) progs),
      bgroup "Smart" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Smart) (Right (ps, expr)))) progs),
      bgroup "Prog" (map (\(mod, ps, expr) -> bench mod $ whnfIO (execute (setMode Tree) (Right (ps, expr)))) progs)
      -- bgroup "pakcs" (map (\(mod, expr) -> bench mod $ whnfIO (callCommand $ "./" ++ mod ++ "-pakcs" )) benchmarks)
      -- bgroup "kics" (map (\(mod, expr) -> bench mod $ whnfIO (callCommand $ "./" ++ mod ++ "-kics" )) benchmarks)
      -- bgroup "pakcs-eval" (map (\(mod, expr) -> bench mod $ whnfIO (runPakcs (mod, expr))) benchmarks)
   ]
  -- mapM_ deleteBinary benchmarks

-- Benchmark programs and the respective main expressions to evaluate.
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

escapePar :: String -> String
escapePar = concatMap (\c -> if c == '(' then "\\(" else if c == ')' then "\\)" else [c])

preparePakcs :: (String, String) -> IO ()
preparePakcs (mod, expr) = do
  callCommand $ binPAKCS ++ " --nocypm :l " ++ mod ++ ".curry :save " ++ escapePar expr ++ " :q"
  callCommand $ "mv " ++ mod ++ " " ++ mod ++ "-pakcs"

runPakcs :: (String, String) -> IO ()
runPakcs (mod, expr) = callCommand $ binPAKCS ++ " --nocypm :l " ++ mod ++ ".curry :eval " ++ escapePar expr ++ " :q"

prepareKics :: (String, String) -> IO ()
prepareKics (mod, expr) = do
  callCommand $ binKICS ++ " --nocypm :l " ++ mod ++ ".curry :save " ++ escapePar expr ++ " :q"
  callCommand $ "mv " ++ mod ++ " " ++ mod ++ "-kics"

deleteBinary :: (String, String) -> IO ()
deleteBinary (mod, expr) = callCommand ("rm " ++ mod ++ "-pakcs") >> callCommand ("rm " ++ mod ++ "-kics")

prepare :: ToolOpts -> (String, String) -> IO (String, [AProg TypeExpr], AFuncDecl TypeExpr)
prepare opts (mod, expr) = loadProg opts (mod ++ ".curry") expr >>= \(Right (ps, expr)) -> return (mod, ps, expr)

setMode :: Mode -> ToolOpts
setMode m = defaultToolOpts { mode = m, time = False}
