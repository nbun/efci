-- {-# OPTIONS_FRONTEND -ddump-flat -Wnone #-}
fac :: Int -> Int
fac m = dumpMemory (case m of
  1 -> 1
  n -> n * (fac (n - 1)))

fac' :: Int -> Int
fac' m = go m 1
  where
    go n acc = dumpMemory (case n of
                   1 -> acc
                   _ -> ((go (n - 1)) (n * acc)))

pointless :: Int -> ()
pointless n = case n of
  0 -> dumpMemory ()
  m -> dumpMemory (pointless (m - 1))