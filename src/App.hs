{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
module App (main, execute, defaultToolOpts, loadProg, ToolOpts(..), Mode(..)) where

import Curry.Frontend.Base.Messages (Message, putErrLn)
import Curry.Frontend.Checks (expandExports)
import Curry.Frontend.CompilerOpts (
  CppOpts (..),
  DumpLevel (..),
  OptimizationOpts (..),
  Options (..),
  WarnFlag (WarnMissingSignatures),
  WarnOpts (..),
  defaultOptions,
  getCompilerOpts,
 )
import Control.Exception (SomeException, try)
import Control.Monad (unless, when)
import Curry.Base.Ident (ModuleIdent, moduleName)
import Curry.Base.Message (ppError, ppMessagesWithPreviews, ppWarning)
import Curry.Base.Monad (runCYIO)
import Curry.Base.Pretty (Doc, Pretty (pPrint))
import Curry.Files.Filenames (
  dropExtension,
  takeFileName,
 )
import Curry.FlatCurry.Annotated.Type (
  AFuncDecl (..),
  AProg (..),
  ARule,
  TypeExpr,
 )
import Curry.Frontend.CurryBuilder (findCurry, processPragmas)
import Curry.Frontend.CurryDeps (Source (..), flatDeps)
import Data.Functor ((<&>))
import Data.List (sort, (\\))
import Data.Map (fromList)
import Data.Maybe (catMaybes)
import GHC.GHCi.Helpers (flushAll)
import Curry.Frontend.Generators (genFlatCurry)
import Curry.Frontend.Generators.GenAnnotatedFlatCurry (genAnnotatedFlatCurry)
import Curry.Frontend.Modules (
  dumpWith,
  exportInterface,
  loadAndCheckModule,
  transModule,
  writeInterface,
 )
import Paths_effective_curry_interpreter (getDataFileName)
import Pipeline
import System.Directory (getCurrentDirectory, removeFile)
import System.FilePath (
  addTrailingPathSeparator,
  normalise,
  pathSeparator,
  takeDirectory,
 )
import System.Timeout (timeout)
import Transformation.FCY2AE (fcyProg2ae, fcyRunner2ae)
import Curry.Frontend.Transformations (qual)
import Type (fdclBdy, reqFuncs, withoutTDecls)
import Effect.General.State (statistics)
import Debug (tracingActive)
-- import Monolith (runMonolithic)
import System.Clock (getTime, Clock (..), TimeSpec (sec, nsec))
import Control.Concurrent (setNumCapabilities)
import GHC.Stats

data Mode = Tree | Codensity | Monolithic | Smart deriving Show

rotateMode :: Mode -> Mode
rotateMode Tree = Codensity
rotateMode Codensity = Monolithic
rotateMode Monolithic = Smart
rotateMode Smart = Tree

data ToolOpts = ToolOpts { showFlatCurryExpr :: Bool, mode :: Mode, time :: Bool} deriving Show

defaultToolOpts :: ToolOpts
defaultToolOpts = ToolOpts { showFlatCurryExpr = False, mode = Smart, time = True}

main :: IO ()
main = do
  setNumCapabilities 16
  (_, _, files, _) <- getCompilerOpts
  let file =
        if null files
          then "Prelude.curry"
          else head files
  loop defaultToolOpts file

loop :: ToolOpts -> FilePath -> IO ()
loop topts file = do
  putStr "λ> "
  flushAll
  input <- getLine
  case input of
    ":q" -> return ()
    ":fcy" -> let topts' = topts {showFlatCurryExpr = not $ showFlatCurryExpr topts} in print topts' >> loop topts' file
    ":o" -> let topts' = topts {mode = rotateMode $ mode topts} in print topts' >> loop topts' file
    ":time" -> let topts' = topts {time = not $ time topts} in print topts' >> loop topts' file

    _ -> do
      let query = case input :: String of
            "" -> "main"
            _ -> input
      res <- execute topts (Left (file, query))
      -- res <- execute topts (Right (preloadProgs, preloadRunner))
      putStrLn ""
      mapM_ (putStrLn . pretty) res
      loop topts file

execute
  :: ToolOpts -> Either (FilePath, String) ([AProg TypeExpr], AFuncDecl TypeExpr) -> IO [Result]
execute topts preloaded = do
  safeRes <- try $ timeout 10000000000 $ case preloaded of
                                         Left (file, query) -> loadProg topts file query >>= uncurry (run topts)
                                         Right (progs, fcyrunner) -> run topts progs fcyrunner
  case safeRes of
    Left e -> putStrLn "" >> print (e :: SomeException) >> return []
    Right (Just res) -> return res
    Right Nothing -> print "Timeout!" >> return []

prepare :: IO (AProg TypeExpr, FilePath)
prepare = do
  dir <- preludeDir
  [p] <- genTAFCY (opts False False [dir]) "Prelude.curry"
  return (p, dir)

preludeDir :: IO FilePath
preludeDir = do
  fn <- getDataFileName "Prelude.curry"
  return (normalise (addTrailingPathSeparator (takeDirectory fn)))

opts :: Bool -> Bool -> [FilePath] -> Options
opts warn dump dirs =
  defaultOptions
    { optCppOpts =
        CppOpts
          { cppRun = True
          , cppDefinitions = fromList [("__KICS2__", 42)]
          }
    , optLibraryPaths = dirs
    , optImportPaths = dirs
    , optWarnOpts =
        if warn
          then
            ( optWarnOpts
                defaultOptions
            )
              { wnWarnFlags =
                  wnWarnFlags
                    (optWarnOpts defaultOptions)
                    \\ [WarnMissingSignatures]
              }
          else (optWarnOpts defaultOptions){wnWarnFlags = []}
    , optOptimizations =
        (optOptimizations defaultOptions){optAddFailed = True}
    }

loadProg :: ToolOpts -> FilePath -> String -> IO ([AProg TypeExpr], AFuncDecl TypeExpr)
loadProg topts file query = do
  let runmod = "Run"
      runmodfn = runmod ++ ".curry"
      qualQuery = if query == "main" then dropExtension file ++ "." ++ query else query
  writeFile runmodfn (genRun (showFlatCurryExpr topts) runmod qualQuery [file])
  currentDir <- getCurrentDirectory
  preludeDir <- preludeDir
  let dirs =
        preludeDir
          : [ ( normalise
                  . addTrailingPathSeparator
                  . takeDirectory
                  . ((currentDir ++ [pathSeparator]) ++)
              )
                runmod
            ]
  -- load modules
  progs <- genTAFCY (opts True True dirs) runmod
  removeFile runmodfn
  let fcyrunner = findRunner (last progs)
  let progs' = map withoutTDecls (reqFuncs progs (fdclBdy fcyrunner))
  return (progs', fcyrunner)

run :: ToolOpts -> [AProg TypeExpr] -> AFuncDecl TypeExpr -> IO [Result]
run topts progs fcyrunner = do
  -- writeFile "Progs.hs" (show progs)
  -- writeFile "Runner.hs" (show fcyrunner)
  start <- getTime Monotonic
  res <- case mode topts of
           Codensity -> do
             let aprogs' = map fcyProg2ae progs
                 runner = fcyRunner2ae (fdclRule fcyrunner)
             runCurryEffectsC aprogs' runner
           Tree -> do
             let aprogs' = map fcyProg2ae progs
                 runner = fcyRunner2ae (fdclRule fcyrunner)
             runCurryEffects @() aprogs' runner
           -- Monolithic -> return $ ([], runMonolithic progs fcyrunner)
           Smart -> do
              let aprogs' = map fcyProg2ae progs
                  runner = fcyRunner2ae (fdclRule fcyrunner)
              runSmartCurryEffects aprogs' runner
  -- when (showFlatCurryExpr topts) $ print fcyrunner\
  end <- getTime Monotonic
  when (time topts) (printTime start end)
  enabled <- getRTSStatsEnabled
  when enabled $ do
      s <- getRTSStats
      putStrLn $ show (max_mem_in_use_bytes s `div` 1000000) ++ "MB allocated"
  let (ti, values) = declutter res
      stats = statistics ti
      sum = foldr (\(_, n) !acc -> n + acc) 0 stats
  -- when tracingActive (print ti)
  when tracingActive (mapM_ print stats >> putStrLn ("Total: " ++ show sum))
  return values

printTime :: TimeSpec -> TimeSpec -> IO ()
printTime start end = do
  -- let diff = fromIntegral (sec end - sec start) +  :: Float
  let diff = fromIntegral (sec end - sec start) + fromIntegral (nsec end - nsec start) / 1e9 :: Float
  putStrLn $ "Time: " ++ show diff ++ "s"

genRun :: Bool -> String -> String -> [String] -> String
genRun dump name expr imports =
  unlines $
    ["{-# OPTIONS_FRONTEND -ddump-flat -Wnone #-}" | dump]
      ++ ["module " ++ name ++ " where", ""]
      ++ map (("import " ++) . dropExtension . takeFileName) imports
      -- ++ ["", "main :: IO ()", "main = print (" ++ expr ++ ")"]
      ++ ["", "main = " ++ expr]

fdclRule :: AFuncDecl ann -> ARule ann
fdclRule (AFunc _ _ _ _ r) = r
fdclRule _ = error "Syntax.fdclExpr: external rule"

genTAFCY :: Options -> String -> IO [AProg TypeExpr]
genTAFCY opts s = do
  unless (isPrefix "Run" s) (putStrLn $ "Loading module " ++ s)
  (res, warns) <- runCYIO $
    do
      fn <- findCurry opts s
      flatDeps opts fn
  unless (null warns) (printMessages ppWarning warns)
  case res of
    Left errs -> error $ show errs
    Right deps -> makeCurry opts deps

compileModule :: Options -> ModuleIdent -> FilePath -> IO (AProg TypeExpr)
compileModule opts m fn = do
  (res, warns) <- runCYIO $
    do
      mdl <- loadAndCheckModule opts m fn
      mdl' <- expandExports opts mdl
      let qmdl' = qual mdl'
      -- qmdl' <- dumpWith opts show pPrint DumpFlatCurry $ qual mdl'
      intf <- uncurry (exportInterface opts) qmdl'
      writeInterface opts (fst mdl') intf
      res@(_, qmdl'') <- transModule opts qmdl'
      return res
  unless (null warns) (printMessages ppWarning warns)
  case res of
    Left errs -> printMessages ppError errs >> error "Loading file failed"
    Right ((env, il), mdl'') -> do
      let res = genAnnotatedFlatCurry False env (snd mdl'') il
      _ <- dumpWith opts show (pPrint . genFlatCurry) DumpFlatCurry (env, res)
      return res

-- | Compiles the given source modules, which must be in topological order.
makeCurry :: Options -> [(ModuleIdent, Source)] -> IO [AProg TypeExpr]
makeCurry opts srcs = mapM process' (zip [1 ..] srcs) <&> catMaybes
 where
  process' (n, (m, Source fn ps is)) = do
    (res, warns) <- runCYIO $ processPragmas opts ps
    unless (null warns) (printMessages ppWarning warns)
    case res of
      Left errs -> error $ show errs
      Right opts' -> do
        prog <- compileModule opts' m fn -- (adjustOptions (n == total) opts') m fn
        return (Just prog)
  process' (_, (m, _)) =
    putStrLn ("Skipping " ++ moduleName m)
      >> return Nothing

isPrefix :: String -> String -> Bool
isPrefix [] _ = True
isPrefix (x : xs) (y : ys)
  | x == y = isPrefix xs ys
isPrefix _ _ = False

findRunner :: AProg ann -> AFuncDecl ann
findRunner (AProg _ _ _ fdecls _) =
  case filter (\(AFunc (_, qn') _ _ _ _) -> "main" == qn') fdecls of
    [] -> error "Missing 'main' definition"
    (x : _) -> x

printMessages :: (Message -> Doc) -> [Message] -> IO ()
printMessages msgType msgs =
  unless
    (null msgs)
    (putErrLn . show =<< ppMessagesWithPreviews msgType (sort msgs))
