last :: Data a => [a] -> a
last xs | xs =:= ys ++ [x] = x where ys, x free

sort :: Data a => ([a] -> [a] -> [a] -> Success) -> [a] -> [a] -> Bool
sort merge xs ys =
   if length xs < 2 then ys =:= xs
   else sort merge (firsthalf xs) us
        && sort merge (secondhalf xs) vs
        && merge us vs ys
   where us,vs free

intMerge :: [Int] -> [Int] -> [Int] -> Bool
intMerge []     ys     zs =  zs =:= ys
intMerge (x:xs) []     zs =  zs =:= x:xs
intMerge (x:xs) (y:ys) zs =
   if (x > y) then intMerge (x:xs) ys us && zs =:= y:us
              else intMerge xs (y:ys) vs && zs =:= x:vs
   where us,vs free
  
firsthalf  xs = take (length xs `div` 2) xs
secondhalf xs = drop (length xs `div` 2) xs