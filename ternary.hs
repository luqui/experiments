{-# LANGUAGE BangPatterns #-}

import Control.Arrow

data T2 = T0 | THalf | T1
    deriving (Eq,Ord,Show)

t2Value :: T2 -> Rational
t2Value T0 = 0
t2Value THalf = 1/2
t2Value T1 = 1

data T2Sum = TS0 | TSHalf | TS1 | TS1Half | TS2
    deriving (Eq,Ord,Show)

t2Sum :: T2 -> T2 -> T2Sum
t2Sum T0 T0 = TS0
t2Sum T0 THalf = TSHalf
t2Sum T0 T1 = TS1
t2Sum THalf T0 = TSHalf
t2Sum THalf THalf = TS1
t2Sum THalf T1 = TS1Half
t2Sum T1 T0 = TS1
t2Sum T1 THalf = TS1Half
t2Sum T1 T1 = TS2

-- bool represents 0 or 1/2
addCarry :: T2Sum -> Bool -> (T2, Bool)
addCarry TS0 False     = (T0, False)
addCarry TS0 True      = (T0, True)
addCarry TSHalf False  = (T0, True)
addCarry TSHalf True   = (THalf, False)
addCarry TS1 False     = (THalf, False)
addCarry TS1 True      = (THalf, True)
addCarry TS1Half False = (THalf, True)
addCarry TS1Half True  = (T1, False)
addCarry TS2 False     = (T1, False)
addCarry TS2 True      = (T1, True)



add' :: [T2] -> [T2] -> Bool -> [T2]  -- wrong
add' (x:xs) (y:ys) c = out : add' xs ys c'
    where
    (out,c') = addCarry (t2Sum x y) c

add xs ys = add' xs ys False

finiteApprox :: [T2] -> Rational
finiteApprox = go (1/2)
    where
    go !a [] = 0
    go !a (x:xs) = a * (t2Value x) + go (a/2) xs

fromApprox :: (Rational -> Rational) -> [T2]
fromApprox f
    | r <= 1/4 = T0 : cont 0
    | r >= 3/4 = T1 : cont (1/2)
    | otherwise = THalf : cont (1/4)
    where
    r = f (1/4)
    cont s = fromApprox (\q -> 2*(f (q/2) - s))

-- Halves a number (/ shifts it to a once-promoted position), smoothing out
-- T1s.  The resulting number will never have two T1s in a row, and will not
-- start with T1.
smooth :: [T2] -> [T2]
smooth = go False
    where
    go False (T1:xs)    = THalf : go False xs
    go False (THalf:xs) = T0 : go True xs
    go False (T0:xs)    = T0 : go False xs
    go True  (T1:xs)    = T1 : go False xs
    go True  (THalf:xs) = THalf : go True xs
    go True  (T0:xs)    = THalf : go False xs
