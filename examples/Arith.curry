-- {-# OPTIONS_FRONTEND -ddump-flat #-}--
module Arith where

fac :: Int -> Int
fac n = case n of
  1 -> 1
  _ -> n * (fac (n - 1))