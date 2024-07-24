data Nat = IHi | I Nat | O Nat
 deriving Show

fromNat :: Nat -> Int
fromNat (O n) = 2 * fromNat n
fromNat (I n) = 2 * fromNat n + 1
fromNat IHi   = 1

toNat :: Int -> Nat
toNat n | n <= 0 = error "Not a positive Integer"
        | n == 1 = IHi
        | even n = O (toNat (n `div` 2))
        | otherwise = I (toNat ((n - 1) `div` 2))

toNat' :: Int -> Nat
toNat' n = if n <= 0
  then error "Not a positive Integer"
  else if n == 1
    then IHi
    else if even n then O (toNat (n `div` 2)) else I (toNat ((n - 1) `div` 2))

addNat :: Nat -> Nat -> Nat
addNat IHi IHi     = O IHi
addNat IHi (O m)   = I m
addNat IHi (I m)   = O (addNat IHi m)
addNat (O n) IHi   = I n
addNat (O n) (O m) = O (addNat n m)
addNat (O n) (I m) = I (addNat n m)
addNat (I n) IHi   = O (addNat IHi n)
addNat (I n) (O m) = I (addNat n m)
addNat (I n) (I m) = O (addNat IHi (addNat n m))

mult :: Nat -> Nat -> Nat
mult n m = case n of
  IHi -> m
  _   -> addNat m (mult (pred n) m)

pred :: Nat -> Nat
pred n = case n of
  (O IHi) -> IHi
  I m     -> O m
  O m     -> I (pred m)

fac :: Nat -> Nat
fac n = case n of
  IHi -> IHi
  _   -> mult n (fac (pred n))

run = fac (O (O IHi))