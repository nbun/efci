module SharingSemantics where

coin :: Bool
coin = True ? False

coini :: Int
coini = 0 ? 1

recList :: [Bool] -> [Bool]
recList xs = case xs of
               []     -> []
               y : ys -> not y : (ys ? recList ys)

dupRT :: (() -> a) -> (a, a)
dupRT rtX = (rtX (), rtX ())

dupShare :: a -> (a, a)
dupShare x = let y = x in (y,y)

duplRT :: (() -> a) -> [a]
duplRT rtX = [rtX (), rtX ()]

duplShare :: a -> [a]
duplShare x = [x, x]