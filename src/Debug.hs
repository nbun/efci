{-# LANGUAGE NoStrict #-}

{- | Debug utilities

This module provides debgging flags that must be enabled/disabled
at compile time to take effect.
-}
module Debug (tracingActive, strace) where

import Debug.HTrace (htrace)

{- | Tracing flag

When enabled:
* Collect tracing information during execution (warning: this slows down the interpreter considerably!)
* Print an overview of the operation distribution after interpretation
-}
tracingActive :: Bool
tracingActive = False

{- | Statistics flag

When enabled:
* Print the final heap layout after running the memoization handler
* Print the heap layout each time the internal heap representation is purged
-}
statistics :: Bool
statistics = False

-- | Statistics trace function, only traces when 'statistics' is enabled
strace :: String -> a -> a
strace s =
    if statistics
        then htrace s
        else id