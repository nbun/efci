-- {-# OPTIONS_FRONTEND -ddump-flat #-}
module Arith where

fac :: Int -> Int
fac n = case n of
  1 -> 1
  _ -> n * (fac (n - 1))

pointless :: Int -> ()
pointless n = case n of
  0 -> dumpMemory ()
  m -> pointless (m - 1)

loop :: Int
loop = loop

sum :: [Int] -> Int -> Int
sum xs acc = case xs of
  []     -> acc
  (y:ys) -> dumpMemory (sum ys $! (acc + y))

main = sum [1, 2] 0

