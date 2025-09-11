{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
module App (main, execute, defaultToolOpts, loadProg, ToolOpts(..), Mode(..), fp2hs) where

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
import Data.List (sort, (\\), intercalate)
import Data.Map (fromList, empty)
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
  takeDirectory, splitPath,
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
import GHC.Utils.Misc (capitalise)
import Monolith (runMonolithic)
import Effect.General.Error (Error(..))

data Mode = Tree | Codensity | Monolithic | Smart deriving Show

rotateMode :: Mode -> Mode
rotateMode Tree = Codensity
rotateMode Codensity = Monolithic
rotateMode Monolithic = Smart
rotateMode Smart = Tree

data ToolOpts = ToolOpts { showFlatCurryExpr :: Bool, mode :: Mode, time :: Bool} deriving Show

defaultToolOpts :: ToolOpts
defaultToolOpts = ToolOpts { showFlatCurryExpr = False, mode = Monolithic, time = True}

main :: IO ()
main = do
  setNumCapabilities 16
  (_, _, files, _) <- getCompilerOpts
  let file = case files of
               [] -> "Prelude.curry"
               (f:_) -> f
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
    ":h"   -> putStrLn (unlines ["Available commands:"
                                 , ":q    - quit"
                                 , ":fcy  - toggle dumping FlatCurry programs"
                                 , ":o    - rotate optimization mode"
                                 , ":time - toggle timing"]) >> loop topts file
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
                                         Left (file, query) -> do
                                          e <- loadProg topts file query
                                          case e of
                                            Left err -> putStrLn err >> return []
                                            Right r -> uncurry (run topts) r
                                         Right (progs, fcyrunner) -> run topts progs fcyrunner
  case safeRes of
    Left e -> putStrLn "" >> print (e :: SomeException) >> return []
    Right (Just res) -> return res
    Right Nothing -> print "Timeout!" >> return []

getPreludeDir :: IO FilePath
getPreludeDir = do
  fn <- getDataFileName "Prelude.curry"
  return (normalise (addTrailingPathSeparator (takeDirectory fn)))

buildOpts :: Bool -> [FilePath] -> Options
buildOpts warn dirs =
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

loadProg :: ToolOpts -> FilePath -> String -> IO (Either String ([AProg TypeExpr], AFuncDecl TypeExpr))
loadProg topts file query = do
  let runmod = "Run"
      runmodfn = runmod ++ ".curry"
      qualQuery = if query == "main" then dropExtension file ++ "." ++ query else query
  writeFile runmodfn (genRun (showFlatCurryExpr topts) runmod qualQuery [file])
  currentDir <- getCurrentDirectory
  preludeDir <- getPreludeDir
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
  progs <- genTAFCY (buildOpts True dirs) runmod
  removeFile runmodfn
  let efcyrunner = findRunner (last progs)
  case efcyrunner of
    Left err -> return $ Left err
    Right fcyrunner -> do
      let progs' = map withoutTDecls (reqFuncs progs (fdclBdy fcyrunner))
      return $ Right (progs', fcyrunner)

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
           Monolithic -> fmap (\x -> ([], EOther $ fmap (\r -> (Data.Map.empty, r)) x)) (runMonolithic progs fcyrunner)
           Smart -> do
              let aprogs' = map fcyProg2ae progs
                  runner = fcyRunner2ae (fdclRule fcyrunner)
              runSmartCurryEffects aprogs' runner
           _ -> error $ "Unimplemented mode: " ++ show (mode topts)
  -- when (showFlatCurryExpr topts) $ print fcyrunner\
  end <- getTime Monotonic
  when (time topts) (printTime start end)
  enabled <- getRTSStatsEnabled
  when enabled $ do
      s <- getRTSStats
      putStrLn $ show (max_mem_in_use_bytes s `div` 1000000) ++ "MB allocated"
  let (ti, values) = declutter res
      stats = statistics ti
      totalSum = foldr (\(_, n) !acc -> n + acc) 0 stats
  -- when tracingActive (print ti)
  when tracingActive (mapM_ print stats >> putStrLn ("Total: " ++ show totalSum))
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

fp2hs :: FilePath -> String
fp2hs fp = case splitPath fp of
            [fn] -> capitalise $ dropExtension fn
            "/" : _ -> error "Total directory paths are not supported"
            xs -> let (ms, fn) = (map (filter (/= pathSeparator)) (init xs), last xs)
                  in intercalate "." (map capitalise ms) ++ "." ++ capitalise (dropExtension fn)

fdclRule :: AFuncDecl ann -> ARule ann
fdclRule (AFunc _ _ _ _ r) = r

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
      transModule opts qmdl'
  unless (null warns) (printMessages ppWarning warns)
  case res of
    Left errs -> printMessages ppError errs >> error "Loading file failed"
    Right ((env, il), mdl'') -> do
      let res' = genAnnotatedFlatCurry False env (snd mdl'') il
      _ <- dumpWith opts show (pPrint . genFlatCurry) DumpFlatCurry (env, res')
      return res'

-- | Compiles the given source modules, which must be in topological order.
makeCurry :: Options -> [(ModuleIdent, Source)] -> IO [AProg TypeExpr]
makeCurry opts srcs = mapM process' (zip [(1 :: Int) ..] srcs) <&> catMaybes
 where
  process' (_, (m, Source fn ps _)) = do
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

findRunner :: AProg ann -> Either String (AFuncDecl ann)
findRunner (AProg _ _ _ fdecls _) =
  case filter (\(AFunc (_, qn') _ _ _ _) -> "main" == qn') fdecls of
    [] -> Left "Missing 'main' definition"
    (f : _) -> case f of
      AFunc _ arity _ _ _ | arity == 0 -> Right f
                          | otherwise -> Left "Expression too general, please provide a (more specific) type."

printMessages :: (Message -> Doc) -> [Message] -> IO ()
printMessages msgType msgs =
  unless
    (null msgs)
    (putErrLn . show =<< ppMessagesWithPreviews msgType (sort msgs))
