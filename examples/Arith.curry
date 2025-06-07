-- {-# OPTIONS_FRONTEND -ddump-flat #-}
module Arith where

fac :: Int -> Int
fac n = case n of
  1 -> 1
  _ -> n * (fac (n - 1))

pointless :: Int -> ()
pointless n = case n of
  0 -> ()
  m -> pointless (m - 1)

loop :: Int
loop = loop