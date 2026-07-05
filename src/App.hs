{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}

{- | Main application module

This module provides the main entry point and REPL interface for the
Curry interpreter. It handles loading Curry programs, executing them
with different optimization modes, and provides an interactive environment.
-}
module App (main, execute, defaultToolOpts, loadProg, ToolOpts (..), Mode (..), fp2hs, withoutBindings) where

import Control.Concurrent (setNumCapabilities)
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
import Curry.Frontend.CurryBuilder (findCurry, processPragmas)
import Curry.Frontend.CurryDeps (Source (..), flatDeps)
import Curry.Frontend.Generators (genFlatCurry)
import Curry.Frontend.Generators.GenAnnotatedFlatCurry (genAnnotatedFlatCurry)
import Curry.Frontend.Modules (
    dumpWith,
    exportInterface,
    loadAndCheckModule,
    transModule,
    writeInterface,
 )
import Curry.Frontend.Transformations (qual)
import Data.Functor ((<&>))
import Data.List (intercalate, sort, (\\))
import Data.Map (empty, fromList)
import Data.Maybe (catMaybes)
import Debug (tracingActive)
import Effect.General.Error (Error (..))
import Effect.General.State (TraceInfo, prettyTI, statistics)
import GHC.GHCi.Helpers (flushAll)
import GHC.Stats
import GHC.Utils.Misc (capitalise)
import InterpFL (runInterpFL)
import Paths_effective_curry_interpreter (getDataFileName)
import Pipeline
import System.Clock (Clock (..), TimeSpec (nsec, sec), getTime)
import System.Directory (getCurrentDirectory, removeFile)
import System.FilePath (
    addTrailingPathSeparator,
    normalise,
    pathSeparator,
    splitPath,
    takeDirectory,
 )
import System.Timeout (timeout)
import Transformation.AE2Result
import Transformation.FCY2AE (fcyProg2ae, fcyRunner2ae)
import Type (fdclBdy, reqFuncs, withoutTDecls)

{- | Execution mode for the interpreter.

* 'Tree': Uses tree-based representation
* 'Codensity': Uses Codensity monad representation
* 'Monolithic': Uses monolithic implementation via InterpFL
* 'Smart': Uses smart view representation
-}
data Mode = Tree | Codensity | Monolithic | Smart deriving (Show)

-- | Rotate to the next execution mode in the cycle: Tree -> Codensity -> Monolithic -> Smart -> Tree
rotateMode :: Mode -> Mode
rotateMode Tree = Codensity
rotateMode Codensity = Monolithic
rotateMode Monolithic = Smart
rotateMode Smart = Tree

{- | Tool options for the interpreter REPL

* 'showFlatCurryExpr': Whether to display FlatCurry expressions
* 'mode': The current execution mode
* 'time': Whether to display execution time
-}
data ToolOpts = ToolOpts {showFlatCurryExpr :: Bool, mode :: Mode, time :: Bool} deriving (Show)

-- | Default tool options: FlatCurry expressions hidden, smart mode, timing enabled
defaultToolOpts :: ToolOpts
defaultToolOpts = ToolOpts{showFlatCurryExpr = False, mode = Smart, time = True}

{- | Main entry point for the Curry interpreter.
Sets up the execution environment and starts the REPL loop.
-}
main :: IO ()
main = do
    setNumCapabilities 16
    (_, _, files, _) <- getCompilerOpts
    let file = case files of
            [] -> "Prelude.curry"
            (f : _) -> f
    loop defaultToolOpts file

-- | REPL loop that reads user input and executes commands or expressions
loop :: ToolOpts -> FilePath -> IO ()
loop topts file = do
    putStr "λ> "
    flushAll
    input <- getLine
    case input of
        ":q" -> return ()
        ":fcy" -> let topts' = topts{showFlatCurryExpr = not $ showFlatCurryExpr topts} in print topts' >> loop topts' file
        ":o" -> let topts' = topts{mode = rotateMode $ mode topts} in print topts' >> loop topts' file
        ":time" -> let topts' = topts{time = not $ time topts} in print topts' >> loop topts' file
        ":h" ->
            putStrLn
                ( unlines
                    [ "Available commands:"
                    , ":q    - quit"
                    , ":fcy  - toggle dumping FlatCurry programs"
                    , ":o    - rotate optimization mode"
                    , ":time - toggle timing"
                    ]
                )
                >> loop topts file
        _ -> do
            let query = case input :: String of
                    "" -> "main"
                    _ -> input
            res <- execute topts (Left (file, query))
            -- res <- execute topts (Right (preloadProgs, preloadRunner))
            putStrLn ""
            mapM_ (putStrLn . pretty) res
            loop topts file

{- | Execute a Curry expression with the given tool options

Takes either a file path and query string, or preloaded programs and runner.
Returns a list of results after execution with timeout handling.
-}
execute
    :: ToolOpts -> Either (FilePath, String) ([AProg TypeExpr], AFuncDecl TypeExpr) -> IO [Result]
execute topts preloaded = do
    safeRes <- try $ timeout 60000000 $ case preloaded of
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

-- | Retrieve the directory of the Prelude.curry file
getPreludeDir :: IO FilePath
getPreludeDir = do
    fn <- getDataFileName "Prelude.curry"
    return (normalise (addTrailingPathSeparator (takeDirectory fn)))

{- | Construct t'Options' for the front end

We use KiCS2 defintions from the Prelude and disable missing signatures
warnings as our @main@ function has no type signature. Furthermore,
we instruct the front end to complete pattern matching with explicit
failures if branches are missing in the source program.
-}
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

{- | Load a Curry program from a file

Creates a temporary Run module containing the query, compiles it to FlatCurry,
and returns either an error message or the loaded programs and runner function.
-}
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

{- | Run a main definition

Expects a function declaration without parameters. Its body is evaluated
using the provided programs and t'ToolOpts'. Besides measuring execution
time, the function also prints RTS statistics (if enabled) and tracing
statistics (if enabled).
-}
run :: ToolOpts -> [AProg TypeExpr] -> AFuncDecl TypeExpr -> IO [Result]
run topts progs fcyrunner = do
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
        Monolithic -> do
            results <- runInterpFL progs fcyrunner
            print $ length results
            return ([], EOther $ fmap (\r -> (Data.Map.empty, r)) results)
        Smart -> do
            let aprogs' = map fcyProg2ae progs
                runner = fcyRunner2ae (fdclRule fcyrunner)
            runSmartCurryEffects aprogs' runner
    -- when (showFlatCurryExpr topts) $ print fcyrunner
    end <- getTime Monotonic
    when (time topts) (printTime start end)
    enabled <- getRTSStatsEnabled
    when enabled $ do
        s <- getRTSStats
        putStrLn $ show (max_live_bytes s `div` 1000000) ++ "MB allocated"
    let (ti, values) = declutter res
    -- when tracingActive (print $ prettyTI $ reverse ti)
    when tracingActive $ printStatistics ti
    return values

-- | Print statistics about primitive and combined operations from trace info
printStatistics :: [TraceInfo] -> IO ()
printStatistics ti = do
    let (primStats, combStats) = statistics ti
        totalPrimSum = foldr (\(_, n) !acc -> n + acc) 0 primStats
        totalCombSum = foldr (\(_, n) !acc -> n + acc) 0 combStats
        printStat (tinfo, cnt) = putStrLn $ "  " ++ prettyTI tinfo ++ ": " ++ show cnt
    putStrLn "Primitive operations:"
    mapM_ printStat primStats
    putStrLn ""
    putStrLn "Combined operations:"
    mapM_ printStat combStats
    putStrLn ""
    putStrLn ("Total (primitive): " ++ show totalPrimSum)
    putStrLn ("Total (combined): " ++ show totalCombSum)
    putStrLn ("Total (all): " ++ show (totalCombSum + totalPrimSum))

-- | Print execution time in seconds
printTime :: TimeSpec -> TimeSpec -> IO ()
printTime start end = do
    let diff = fromIntegral (sec end - sec start) + fromIntegral (nsec end - nsec start) / 1e9 :: Float
    putStrLn $ "Time: " ++ show diff ++ "s"

-- | Generate a temporary Run module for executing expressions
genRun :: Bool -> String -> String -> [String] -> String
genRun dump name expr imports =
    unlines $
        ["{-# OPTIONS_FRONTEND -ddump-flat -Wnone #-}" | dump]
            ++ ["module " ++ name ++ " where", ""]
            ++ map (("import " ++) . dropExtension . takeFileName) imports
            -- ++ ["", "main :: IO ()", "main = print (" ++ expr ++ ")"]
            ++ ["", "main = " ++ expr]

-- | Convert a file path to a Haskell module name
fp2hs :: FilePath -> String
fp2hs fp = case splitPath fp of
    [fn] -> capitalise $ dropExtension fn
    "/" : _ -> error "Total directory paths are not supported"
    xs ->
        let (ms, fn) = (map (filter (/= pathSeparator)) (init xs), last xs)
        in  intercalate "." (map capitalise ms) ++ "." ++ capitalise (dropExtension fn)

-- | Retrieve the rule of a function declaration
fdclRule :: AFuncDecl ann -> ARule ann
fdclRule (AFunc _ _ _ _ r) = r

-- | Find, load, and generate FlatCurry for a module and its dependencies
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

-- | Compile a single Curry module to FlatCurry
compileModule :: Options -> ModuleIdent -> FilePath -> IO (AProg TypeExpr)
compileModule opts m fn = do
    (res, warns) <- runCYIO $
        do
            mdl <- loadAndCheckModule opts m fn
            mdl' <- expandExports opts mdl
            let qmdl' = qual mdl'
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

{- | Compiles the given source modules, which must be in topological order.
Processes each module with pragmas, loads dependencies, and generates FlatCurry.
-}
makeCurry :: Options -> [(ModuleIdent, Source)] -> IO [AProg TypeExpr]
makeCurry opts srcs = mapM process' (zip [(1 :: Int) ..] srcs) <&> catMaybes
  where
    process' (_, (m, Source fn ps _)) = do
        (res, warns) <- runCYIO $ processPragmas opts ps
        unless (null warns) (printMessages ppWarning warns)
        case res of
            Left errs -> error $ show errs
            Right opts' -> do
                prog <- compileModule opts' m fn
                return (Just prog)
    process' (_, (m, _)) =
        putStrLn ("Skipping " ++ moduleName m)
            >> return Nothing

-- | Check whether the first parameter is a prefix of the second
isPrefix :: String -> String -> Bool
isPrefix [] _ = True
isPrefix (x : xs) (y : ys)
    | x == y = isPrefix xs ys
isPrefix _ _ = False

-- | Find the main function runner in a FlatCurry program
findRunner :: AProg ann -> Either String (AFuncDecl ann)
findRunner (AProg _ _ _ fdecls _) =
    case filter (\(AFunc (_, qn') _ _ _ _) -> "main" == qn') fdecls of
        [] -> Left "Missing 'main' definition"
        (f : _) -> case f of
            AFunc _ arity _ _ _
                | arity == 0 -> Right f
                | otherwise -> Left "Expression too general, please provide a (more specific) type."

-- | Print a list of messages
printMessages :: (Message -> Doc) -> [Message] -> IO ()
printMessages msgType msgs =
    unless
        (null msgs)
        (putErrLn . show =<< ppMessagesWithPreviews msgType (sort msgs))