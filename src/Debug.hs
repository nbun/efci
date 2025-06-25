{-# LANGUAGE NoStrict #-}
module Debug  (tracingActive, ctrace, strace) where

import Debug.HTrace (htrace)

debug :: Bool
debug = False

tracingActive :: Bool
tracingActive = False

ctrace :: String -> a -> a
ctrace s =
    if debug
        then htrace s
        else id

statistics :: Bool
statistics = False

strace :: String -> a -> a
strace s =
    if statistics
        then htrace s
        else id