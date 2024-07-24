module PermSort where

sort :: Ord a => [a] -> [a]
sort l | isSorted p = p where p = perm l

isSorted :: Ord t => [t] -> Bool
isSorted ys = case ys of
                   []     -> True
                   (x:xs) -> isSorted' x xs

isSorted' :: Ord t => t -> [t] -> Bool
isSorted' x xs = case xs of
                      []     -> True
                      (y:ys) -> x <= y && isSorted' y ys

perm :: [a] -> [a]
perm ys = case ys of
               []     -> []
               (x:xs) -> insert x (perm xs)

insert :: a -> [a] -> [a]
insert  x xs = (x : xs) ? (insert2 x xs)

insert2 :: a -> [a] -> [a]
insert2 x xs = case xs of
                    (y:ys) -> y : insert x ys
