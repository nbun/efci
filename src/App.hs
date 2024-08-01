{-# LANGUAGE TypeApplications #-}
module App where

import Base.Messages (Message, putErrLn)
import Checks (expandExports)
import CompilerOpts (
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
import Control.Monad (unless)
import Curry.Base.Ident (ModuleIdent, moduleName)
import Curry.Base.Message (ppError, ppMessagesWithPreviews, ppWarning)
import Curry.Base.Monad (runCYIO)
import Curry.Base.Pretty (Doc, Pretty (pPrint))
import Curry.Files.Filenames (
  addOutDirModule,
  dropExtension,
  takeFileName,
 )
import Curry.FlatCurry.Annotated.Type (
  AFuncDecl (..),
  AProg (..),
  ARule,
  TypeExpr,
 )
import CurryBuilder (findCurry, processPragmas)
import CurryDeps (Source (..), flatDeps)
import Data.Functor ((<&>))
import Data.List (sort, (\\))
import Data.Map (fromList)
import Data.Maybe (catMaybes)
import Free (Prog)
import GHC.GHCi.Helpers (flushAll)
import Generators (genFlatCurry)
import Generators.GenAnnotatedFlatCurry (genAnnotatedFlatCurry)
import Modules (
  dumpWith,
  exportInterface,
  loadAndCheckModule,
  transModule,
  writeInterface,
 )
import Paths_algebraic_effect_curry_interpreter (getDataFileName)
import Pipeline
import System.Directory (getCurrentDirectory, removeFile)
import System.FilePath (
  addTrailingPathSeparator,
  normalise,
  pathSeparator,
  takeDirectory,
 )
import System.Timeout (timeout)
import Transformation.FCY2AE (CurryEffects, fcyProg2ae, fcyRunner2ae)
import Transformations (qual)
import Type (AEProg)

data ToolOpts = ToolOpts { showFlatCurryExpr :: Bool, optimize :: Bool}

defaultToolOpts :: ToolOpts
defaultToolOpts = ToolOpts { showFlatCurryExpr = False, optimize = True}

main :: IO ()
main = do
  (_, _, files, _) <- getCompilerOpts
  prelude <- prepare
  let file =
        if null files
          then "Prelude.curry"
          else head files
  loop defaultToolOpts prelude file

loop :: ToolOpts -> (AProg TypeExpr, FilePath) -> FilePath -> IO ()
loop topts prelude file = do
  putStr "λ> "
  flushAll
  input <- getLine
  case input of
    ":q" -> return ()
    ":fcy" -> loop (topts {showFlatCurryExpr = not $ showFlatCurryExpr topts}) prelude file
    ":o" -> loop (topts {optimize = not $ optimize topts}) prelude file

    _ -> do
      let query = case input :: String of
            "" -> "main"
            _ -> input
      res <- execute topts prelude file query
      putStrLn ""
      mapM_ (putStrLn . pretty) res
      loop topts prelude file

execute
  :: ToolOpts -> (AProg TypeExpr, FilePath) -> String -> String -> IO [Result]
execute topts prelude file query = do
  let runmod = "Run"
      runmodfn = runmod ++ ".curry"
  writeFile runmodfn (genRun (showFlatCurryExpr topts) runmod query [file])
  safeRes <- try $ timeout 100000000 $ execRun topts prelude runmod
  removeFile runmodfn
  case safeRes of
    Left e -> putStrLn "" >> print (e :: SomeException) >> return []
    Right (Just res) -> return res
    Right Nothing -> print "Timeout!" >> return []

prepare :: IO (AProg TypeExpr, FilePath)
prepare = do
  fn <- getDataFileName "Prelude.curry"
  let dir = normalise (addTrailingPathSeparator (takeDirectory fn))
  [p] <- genTAFCY (opts False False [dir]) "Prelude.curry"
  return (p, dir)

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

execRun :: ToolOpts -> (AProg TypeExpr, FilePath) -> FilePath -> IO [Result]
execRun topts (prelude, preludeDir) file = do
  currentDir <- getCurrentDirectory
  let dirs =
        preludeDir
          : [ ( normalise
                  . addTrailingPathSeparator
                  . takeDirectory
                  . ((currentDir ++ [pathSeparator]) ++)
              )
                file
            ]
  -- load modules
  progs <- genTAFCY (opts True True dirs) file
  let fcyrunner = findRunner (last progs)
  res <- case optimize topts of
           True -> do
             let aprogs' = map fcyProg2ae progs
                 runner = fcyRunner2ae (fdclRule fcyrunner)
             runCurryEffectsC @() aprogs' runner
           False -> do
             let aprogs' = map fcyProg2ae progs
                 runner = fcyRunner2ae (fdclRule fcyrunner)
             runCurryEffects @() aprogs' runner
  -- when (showFlatCurryExpr topts) $ print fcyrunner
  return (declutter res)

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
  res <- runCYIO $
    do
      fn <- findCurry opts s
      flatDeps opts fn
  case res of
    Left errs -> error $ show errs
    Right (deps, warns) -> do
      unless (null warns) (printMessages ppWarning warns)
      makeCurry opts deps

compileModule :: Options -> ModuleIdent -> FilePath -> IO (AProg TypeExpr)
compileModule opts m fn = do
  res <- runCYIO $
    do
      mdl <- loadAndCheckModule opts m fn
      mdl' <- expandExports opts mdl
      let qmdl' = qual mdl'
      -- qmdl' <- dumpWith opts show pPrint DumpFlatCurry $ qual mdl'
      intf <- uncurry (exportInterface opts) qmdl'
      writeInterface opts (fst mdl') intf
      res@(_, qmdl'') <- transModule opts qmdl'
      return res
  case res of
    Left errs -> printMessages ppError errs >> error "Loading file failed"
    Right (((env, il), mdl''), warns) -> do
      unless (null warns) (printMessages ppWarning warns)
      let res = genAnnotatedFlatCurry False env (snd mdl'') il
      _ <- dumpWith opts show (pPrint . genFlatCurry) DumpFlatCurry (env, res)
      return res

-- | Compiles the given source modules, which must be in topological order.
makeCurry :: Options -> [(ModuleIdent, Source)] -> IO [AProg TypeExpr]
makeCurry opts srcs = mapM process' (zip [1 ..] srcs) <&> catMaybes
 where
  process' (n, (m, Source fn ps is)) = do
    res <- runCYIO $ processPragmas opts ps
    case res of
      Left errs -> error $ show errs
      Right (opts', warns) -> do
        unless (null warns) (printMessages ppWarning warns)
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
