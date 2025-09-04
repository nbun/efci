fac :: Int -> Int
fac m = dumpMemory $ case m of
  1 -> 1
  n -> n * (fac (n - 1))

fac' :: Int -> Int
fac' m = go (m - 1) m
  where
    go n acc = (case n of
                   1 -> dumpMemory $ acc
                   _ -> (go (n - 1)) $## (n * acc))

pointless :: Int -> ()
pointless n = case n of
  0 -> ()
  m -> dumpMemory $ pointless $! (m - 1)