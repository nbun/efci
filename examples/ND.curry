module ND where

import Binary

data Color = R | G | B

data List a = Nil | Cons a (List a)

insert :: a -> List a -> List a
insert a Nil = Cons a Nil
insert a (Cons x xs) = Cons a (Cons x xs)
insert a (Cons x xs) = Cons x (insert a xs)

coin :: Int
coin = 0
coin = 1

fac :: Int -> Int
fac n = case n of
  1 -> 1
  _ -> n * (n - 1)


data Test = Test (Int -> Int)

t = Test (+1)

test :: Test -> Int
test (Test f) = f 2

data Test2 = Test2 Int

t2 = Test2 42

test2 :: Test2 -> Int
test2 (Test2 i) = i + 1

run :: Int
-- run = 1 + 2
-- run = let f = (+1) in f 2
run = double (0 ? 1)

double :: Int -> Int
double x = x + x