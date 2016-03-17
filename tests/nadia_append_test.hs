import Data.List
import Control.Arrow

appendNadia :: [a] -> [a] -> [a]
appendNadia xs [] = xs
appendNadia [] ys = ys
appendNadia (x8:x9) (x4:x5) = x4:(appendNadia x9 (x4:x5))

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

append :: [a] -> [a] -> [a]
append xs ys = foldr (:) ys xs

reverse' :: [a] -> [a]
reverse' xs = foldl (flip (:)) [] xs

bagsum xs = map (head &&& length) (group (sort xs))

map' :: (a -> b) -> [a] -> [b]
map' f xs = foldr (\x acc -> f x : acc) [] xs

map'' :: (a -> b) -> [a] -> [b]
map'' f xs = foldr ((:) . f) [] xs

drop' :: Int -> [a] -> [a]
drop' n xs = snd (splitAt n xs)

sortByLength :: [[a]] -> [[a]]
sortByLength xss = sortBy (\xs ys -> compare (length xs) (length ys)) xss

sortByLength' :: [[a]] -> [[a]]
sortByLength' = sortBy (curry ((uncurry compare) . (length *** length)))

cmp :: Ord a => [a] -> [a] -> Ordering
cmp = curry ((uncurry compare) . (length *** length))

dropmin :: [[Int]] -> [[Int]]
dropmin xss = map (\xs -> filter (/= minimum xs) xs) xss