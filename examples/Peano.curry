data Peano = O | S Peano
  deriving Show

add :: Peano -> Peano -> Peano
add n m = case n of
  O    -> m
  S n' -> S (add n' m)

sub :: Peano -> Peano -> Peano
sub x y | (add y z =:= x) = z where z free

pred :: Peano -> Peano
pred O     = O
pred (S n) = n

mult :: Peano -> Peano -> Peano
mult n m = case n of
  O    -> O
  S n' -> add m (mult n' m)

fac :: Peano -> Peano
fac O     = (S O)
fac (S n) = mult (S n) (fac n)

i2p :: Int -> Peano
i2p n = case n of
  0 -> O
  m -> S (i2p (m - 1))

p2i :: Peano -> Int
p2i p = case p of
          O -> 0
          (S q) -> 1 + p2i q

pointless :: Peano -> ()
pointless n = case n of
  O -> ()
  S m -> pointless m