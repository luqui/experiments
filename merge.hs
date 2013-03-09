merge :: (Ord a) => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

merges :: (Ord a) => [[a]] -> [a]
merges [] = []
merges ([]:xss) = merges xss
merges ((x:xs):xss) = x : merge xs (merges xss)

npfree :: Integer -> [Integer]
npfree k = merges [ [ m*n^k | m <- [1..] ] | n <- [2..] ]

nprime :: a -> [Integer]
nprime x = seq x $ merges [ [ m*n | m <- [n..] ] | n <- [2..] ]

without :: (Ord a) =>[a] -> [a] -> [a]
without _ [] = []
without [] xs = xs
without (x:xs) (y:ys)
    = case compare x y of
        LT -> without xs (y:ys)
        EQ -> without (x:xs) ys
        GT -> y : without (x:xs) ys

squish :: (Eq a) => [a] -> [a]
squish [] = []
squish [x] = [x]
squish (x:x':xs)
    | x == x' = squish (x':xs)
    | otherwise = x : squish (x':xs)
