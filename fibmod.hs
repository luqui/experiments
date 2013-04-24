import qualified Data.Map as Map
import Control.Arrow
import Math.NumberTheory.Primes.Factorisation (factorise)

type Z = Integer

fibmod :: Z -> [Z]
fibmod n = let f = 0:1:zipWith (+*) f (tail f) in f
    where
    x +* y = (x + y) `mod` n

adjacent :: [a] -> [(a,a)]
adjacent xs = zip xs (tail xs)

cycleIndices :: (Ord a) => [a] -> Maybe (Int,Int)
cycleIndices = go Map.empty 0
    where
    go _ _ [] = Nothing
    go m i' (x:xs)
        | Just i <- Map.lookup x m = Just (i,i')
        | otherwise                = (go (Map.insert x i' m) $! i'+1) xs

fibcycle :: Z -> Int
fibcycle = maybe 0 (uncurry subtract) . cycleIndices . adjacent . fibmod

recordsOn :: (Ord b) => (a -> b) -> [a] -> [a]
recordsOn measure [] = []
recordsOn measure (x:xs) = x : go (measure x) xs
    where
    go r [] = []
    go r (x:xs)
        | mx > r    = x : go mx xs
        | otherwise = go r xs
        where
        mx = measure x
