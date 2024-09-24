{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE TypeOperators #-}

module DelContExamples where

import qualified Control.Exception as E
import Control.Exception.Base (NoMatchingContinuationPrompt (..))
import Data.Either
import Data.Foldable (for_)
import Data.Functor (void)
import Data.Functor.Sum (Sum (..))
import Data.Maybe (fromMaybe, maybe)
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))
import GHC.Stack (HasCallStack)
import System.Environment
import System.IO.Unsafe
import Prelude hiding (log)

newtype Mom a = Mom (IO a)
    deriving newtype (Functor, Applicative, Monad)

-- Unsafe primitives

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: Mom (PromptTag a)
newPromptTag =
    Mom
        ( IO
            ( \s -> case newPromptTag# s of
                (# s', tag #) -> (# s', PromptTag tag #)
            )
        )

prompt :: PromptTag a -> Mom a -> Mom a
prompt (PromptTag tag) (Mom (IO m)) = Mom (IO (prompt# tag m))

control0 :: PromptTag a -> ((Mom b -> Mom a) -> Mom a) -> Mom b
control0 (PromptTag tag) f =
    Mom (IO (control0# tag (\k -> case f (\(Mom (IO a)) -> Mom (IO (k a))) of Mom (IO b) -> b)))

-- Look Ma', no IO!
run :: Mom a -> Maybe a
run (Mom m) =
    unsafePerformIO
        (E.catch (Just <$> m) \NoMatchingContinuationPrompt -> pure Nothing)

data Exception e a
    = Throw e

throw :: Exception e % r -> e -> Mom a
throw tag e = control0 tag \_ -> pure (Op (Throw e))

catch :: (Exception e % a -> Mom a) -> (e -> Mom a) -> Mom a
catch f onThrow = do
    tag <- newPromptTag
    handle tag (f tag)
  where
    handle tag action = do
        next <- prompt tag (Pure <$> action)
        case next of
            Op (Throw e) -> onThrow e
            Pure a -> pure a
type f % r = PromptTag (Free f r)

data Free f r
    = Op (f (Free f r))
    | Pure r

try :: (Exception e % Either e a -> Mom a) -> Mom (Either e a)
try f = catch (\tag -> Right <$> f tag) (\e -> pure (Left e))

testThrow :: IO ()
testThrow = do
    assert (isRight' (run (try (\_ -> pure "Result"))))
    assert (isLeft' (run (try (\exc -> throw exc "Error"))))
  where
    isRight' = maybe False isRight
    isLeft' = maybe False isLeft

-- Minimalistic unit testing framework
assert :: (HasCallStack) => Bool -> IO ()
assert True = pure ()
assert False = error "Assertion failed"

data Out o a
    = Output o (Mom () -> Mom a)

output :: Out o % r -> o -> Mom ()
output tag o = control0 tag \continue -> pure (Op (Output o continue))

log :: Out String % r -> String -> Mom ()
log = output

fibonacci :: Out Int % r -> Mom a
fibonacci out = fib 0 1
  where
    fib !a !b = do
        output out a
        fib b (a + b)

collect :: (Out o % () -> Mom ()) -> [o]
collect f = runList do
    tag <- newPromptTag
    handle tag (Pure <$> f tag)
  where
    handle tag action = do
        next <- prompt tag action
        case next of
            Op (Output o continue) ->
                pure (o : runList (handle tag (continue (pure ()))))
            Pure () -> pure []
    runList = fromMaybe [] . run

testFibonacci :: IO ()
testFibonacci =
    assert
        ( take 8 (collect fibonacci)
            == [0, 1, 1, 2, 3, 5, 8, 13]
        )

tracedCatch :: Out String % r -> Mom Bool
tracedCatch out = catch this onThrow
  where
    this exc = do
        log out "Start"
        _ <- throw exc "Boom"
        log out "This is unreachable"
        pure False
    onThrow msg = do
        log out ("Error: " ++ msg)
        pure True

testTracedCatch :: IO ()
testTracedCatch =
    assert
        ( collect (void . tracedCatch)
            == [ "Start"
               , "Error: Boom"
               ]
        )

discardOutput :: (Out o % a -> Mom a) -> Mom a
discardOutput f = do
    tag <- newPromptTag
    handle tag (Pure <$> f tag)
  where
    handle tag action = do
        next <- prompt tag action
        case next of
            Op (Output _o continue) -> handle tag (continue (pure ()))
            Pure a -> pure a

testDiscard :: IO ()
testDiscard =
    assert (run (discardOutput tracedCatch) == Just True)

data In i a
    = Input (Mom i -> Mom a)

input :: In i % r -> Mom i
input tag = control0 tag \continue -> pure (Op (Input continue))

csum :: In Int % r -> Out Int % r -> Mom a
csum inp out = go 0
  where
    go !acc = do
        n <- input inp
        let acc' = acc + n
        output out acc'
        go acc'

listInput :: [i] -> (In i % a -> Mom a) -> Mom (Maybe a)
listInput is f = do
    tag <- newPromptTag
    catch
        (\exc -> handle exc tag is (Pure <$> f tag))
        (\() -> pure Nothing)
  where
    handle exc tag is action = do
        next <- prompt tag action
        case next of
            Op (Input continue)
                | i : is' <- is -> handle exc tag is' (continue (pure i))
                | otherwise -> handle exc tag [] (continue (throw exc ()))
            Pure a -> pure (Just a)

testCsum :: IO ()
testCsum =
    assert
        ( ( collect \out ->
                void $ listInput [1 .. 5] \inp ->
                    csum inp out
          )
            == [1, 3, 6, 10, 15]
        )

connect :: (Out x % a -> Mom a) -> (In x % a -> Mom a) -> Mom a
connect producer consumer = do
    out <- newPromptTag
    inp <- newPromptTag
    handleI out inp (Pure <$> producer out) (Pure <$> consumer inp)
  where
    handleI out inp produce consume = do
        next <- prompt inp consume
        case next of
            Op (Input continue) -> handleO out inp produce continue
            Pure a -> pure a
    handleO out inp produce consuming = do
        next <- prompt out produce
        case next of
            Op (Output o continue) ->
                handleI out inp (continue (pure ())) (consuming (pure o))
            Pure a -> pure a

csum2 :: In Int % () -> Out Int % () -> Mom ()
csum2 inp out = connect (\out' -> csum inp out') (\inp' -> csum inp' out)

testConnect :: IO ()
testConnect =
    assert
        ( ( collect \out ->
                void $ listInput [1 .. 5] \inp ->
                    csum2 inp out
          )
            == [1, 4, 10, 20, 35]
        )

printOutput :: (Out String % () -> Mom ()) -> IO ()
printOutput f = momToIO do
    tag <- newPromptTag
    handle tag (Pure <$> f tag)
  where
    handle tag action = do
        next <- prompt tag action
        case next of
            Op (Output o continue) -> pure do
                putStrLn o
                momToIO (handle tag (continue (pure ())))
            Pure () -> pure (pure ())
    momToIO = fromMaybe (pure ()) . run

readInput :: (In String % () -> Mom ()) -> IO ()
readInput f = momToIO do
    tag <- newPromptTag
    handle tag (Pure <$> f tag)
  where
    handle tag action = do
        next <- prompt tag action
        case next of
            Op (Input continue) -> pure do
                i <- getLine
                momToIO (handle tag (continue (pure i)))
            Pure () -> pure (pure ())
    momToIO = fromMaybe (pure ()) . run
data State s a
    = Get (Mom s -> Mom a)
    | Put s (Mom () -> Mom a)

get :: State s % r -> Mom s
get tag = control0 tag \continue -> pure (Op (Get continue))


put :: State s % r -> s -> Mom ()
put tag s = control0 tag \continue -> pure (Op (Put s continue))

runState :: s -> (State s % a -> Mom a) -> Mom (s, a)
runState s0 f = do
    tag <- newPromptTag
    handle tag s0 (Pure <$> f tag)
  where
    handle tag s action = do
        next <- prompt tag action
        case next of
            Op (Get continue) -> handle tag s (continue (pure s))
            Op (Put s' continue) -> handle tag s' (continue (pure ()))
            Pure a -> pure (s, a)

incr :: State Int % r -> Mom ()
incr st = do
    n <- get st
    put st (n + 1)

logState :: Out String % r -> State Int % s -> Mom ()
logState out st = do
    n <- get st
    log out (show n)

incr2 :: Out String % r -> State Int % s -> Mom ()
incr2 out st = do
    incr st
    logState out st
    incr st
    logState out st

testState :: IO ()
testState = do
    assert ((collect \out -> runState 0 (incr2 out) *> pure ()) == ["1", "2"])
    assert (run (discardOutput \out -> runState 0 (incr2 out)) == Just (2, ()))

data Nondet a where
    Choose :: [x] -> (Mom x -> Mom a) -> Nondet a

choose :: Nondet % r -> [x] -> Mom x
choose tag xs = control0 tag \continue -> pure (Op (Choose xs continue))

nameTheorems :: Nondet % r -> Mom String
nameTheorems nd = do
    name1 <- choose nd ["Church", "Curry"]
    name2 <- choose nd ["Turing", "Howard"]
    result <- choose nd ["thesis", "isomorphism"]
    pure (name1 ++ "-" ++ name2 ++ " " ++ result)

enumerate :: (Nondet % a -> Mom a) -> Out a % r -> Mom ()
enumerate f out = do
    tag <- newPromptTag
    handle tag (Pure <$> f tag)
  where
    handle tag action = do
        next <- prompt tag action
        case next of
            Op (Choose xs continue) -> for_ xs (handle tag . continue . pure)
            Pure a -> output out a

testEnumerate :: IO ()
testEnumerate = do
    assert
        ( collect (enumerate nameTheorems)
            == [ "Church-Turing thesis"
               , "Church-Turing isomorphism"
               , "Church-Howard thesis"
               , "Church-Howard isomorphism"
               , "Curry-Turing thesis"
               , "Curry-Turing isomorphism"
               , "Curry-Howard thesis"
               , "Curry-Howard isomorphism"
               ]
        )

data Conc a
    = Fork (Mom ()) (Mom () -> Mom a)
    | Yield (Mom () -> Mom a)

fork :: Conc % r -> Mom () -> Mom ()
fork tag thread = control0 tag \continue -> pure (Op (Fork thread continue))

yield :: Conc % r -> Mom ()
yield tag = control0 tag \continue -> pure (Op (Yield continue))

simpleThread :: Out String % r -> Conc % s -> Int -> Mom ()
simpleThread out conc n = do
    log out (show n)
    yield conc
    log out (show n)
    yield conc
    log out (show n)
    yield conc

interleave123 :: Out String % r -> Conc % s -> Mom ()
interleave123 out conc = do
    fork conc (simpleThread out conc 1)
    fork conc (simpleThread out conc 2)
    fork conc (simpleThread out conc 3)

runConc :: (Conc % () -> Mom ()) -> Mom ()
runConc f = do
    tag <- newPromptTag
    handle tag [Pure <$> f tag]
  where
    handle tag [] = pure ()
    handle tag (thread : threads) = do
        next <- prompt tag thread
        case next of
            Op (Yield continue) -> handle tag (threads ++ [continue (pure ())])
            Op (Fork th continue) -> handle tag (continue (pure ()) : threads ++ [Pure <$> th])
            Pure () -> handle tag threads

testInterleave :: IO ()
testInterleave =
    assert
        ( (collect \out -> runConc \conc -> interleave123 out conc)
            == ["1", "2", "3", "1", "2", "3", "1", "2", "3"]
        )

main :: IO ()
main = do
    testThrow
    testFibonacci
    testTracedCatch
    testDiscard
    testCsum
    testConnect
    testState
    testEnumerate
    testInterleave
    putStrLn "All tests passed!"

-- >>> main
