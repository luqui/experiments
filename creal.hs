{-# LANGUAGE DataKinds #-}

import Data.CReal
import Data.CReal.Converge
import Data.CReal.Internal
import Data.Maybe (fromMaybe)

sigma :: [CReal p] -> CReal p
sigma = fromMaybe (error "does not converge") . converge . scanl (+) 0

-- (a+b)^n = sum_i binomial(n,i) a^i b^(n-i)

factorial :: Integer -> Integer
factorial n = product [1..n]

binomial :: Integer -> Integer -> Integer
binomial n k
    | k <= n = factorial n `div` (factorial k * factorial (n-k))
    | otherwise = 0

-- sum_i a_i (z-c)^i
--   = sum_i z^i a_i (sum_j binomial(j,i) c^j)

transport :: CReal p -> [CReal p] -> [CReal p]
transport c as =
    [ sigma $ zipWith (\j a -> fromInteger (binomial j i) * c^(j-i) * a) 
                      [i..] (drop (fromInteger i) as)
    | i <- [0..] 
    ] 


result = (.)
