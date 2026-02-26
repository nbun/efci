module PermSort where

sort :: Ord a => [a] -> [a]
sort l | isSorted p = p 
  where p = perm l

isSorted :: Ord a => [a] -> Bool
isSorted []       = True
isSorted [_]      = True
isSorted (x:y:ys) = x <= y && isSorted (y:ys)

perm :: [a] -> [a]
perm []     = []
perm (x:xs) = insert x (perm xs)

insert :: a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) = x:y:ys ? y : (insert x ys)