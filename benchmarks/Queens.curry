-- Compute the number of solutions to queens placements.
-- This implementation uses prelude operations and list comprehensions,
-- thus, higher-order operations like `map`.

data Nat = O | S Nat
  deriving Eq

instance Enum Nat where
  succ = S
  pred (S n) = n
  pred O     = failed

  fromEnum O = 0
  fromEnum (S n) = fromEnum n + 1

  toEnum n | n == 0    = O
           | n >  0    = S (toEnum (n-1))
           | otherwise = failed

queens :: Nat -> Int
queens nq = length (gen nq nq)

gen :: Nat -> Nat -> [[Nat]]
gen nq n = if n==O
          then [[]]
          else [ q:b | b <- gen nq (pred n), q <- [S O .. nq], safe q (S O) b]

add :: Nat -> Nat -> Nat
add O     y = y
add (S x) y = S (add x y)

sub :: Nat -> Nat -> Maybe Nat
sub x     O     = Just x
sub (S x) (S y) = sub x y
sub O     (S _) = Nothing

safe :: Nat -> Nat -> [Nat] -> Bool
safe _ _ [] = True
safe x d (q:l) = x /= q && x /= add q d && Just x /= sub q d && safe x (succ d) l

queens_10, queens_11 :: Int
queens_10 = queens (S (S (S (S (S (S (S (S (S (S O))))))))))
queens_11 = queens (S (S (S (S (S (S (S (S (S (S (S O)))))))))))

main :: Int
main = queens_10
