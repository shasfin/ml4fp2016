import Data.List

append :: [a] -> [a] -> [a]
append xs [] = xs
append [] ys = ys
append (x8:x9) (x4:x5) = x4:(append x9 (x4:x5))

tails' xs = scanr (:) [] xs

triangular :: Int -> Int
triangular n = sum [1..n]

tetrahedral :: Int -> Int
tetrahedral n = sum (map triangular [1..n])

tetrahedral' :: Int -> Int
tetrahedral' n = scanl1 (+) (scanl1 (+) [0..]) !! n

tetrahedral''' n = foldl1 (+) (scanl1 (+) (enumFromTo 1 n))

--tetrahedral'' :: Int -> Int
--tetrahedral'' n = sum (sum )

average :: [Int] -> Int
average xs = (sum xs) `div` (length xs)


movingAverage :: Int -> [Int] -> [Int]
movingAverage n xs = map (average . take n) (init $ tails xs)

maximum' :: [Int] -> Int
maximum' xs = foldr max (head xs) xs

prime n = minimum (1 : (map (mod n) (enumFromTo 2 (subtract 1 n))))

movingSum n xs = tail $ scanl (+) 0 (zipWith (-) xs (replicate n 0 ++ xs))

movingSum' n xs = scanl1 (+) (zipWith (-) xs (replicate n 0 ++ xs))

water h = sum $ 
      zipWith (-) 
        (zipWith min (scanl1 max h) (scanr1 max h))
        h

horner p x = foldl1 ((+) . (x *)) p