module Debug where

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