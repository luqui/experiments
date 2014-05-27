{-# LANGUAGE BangPatterns, DataKinds, PolyKinds, ConstraintKinds, RankNTypes, TupleSections #-}

import Control.Arrow
import Control.Applicative
import Partial
import Data.Glb (HasGlb(glb), flatGlb)
import Data.Lub (HasLub(lub), flatLub)

data Place = H Place

data T2 p = T0 | THalf | T1
    deriving (Eq, Ord, Show)

instance HasGlb (T2 p) where glb = flatGlb
instance HasLub (T2 p) where lub = flatLub
    
-- if we know that the input is at least half, then we know snd of the output
-- is THalf.
addHalf :: T2 (H p) -> (T2 (H p), T2 p)
addHalf T0    = (THalf, T0)
addHalf THalf = (T1, T0)
addHalf T1    = (THalf, THalf)

addThreeHalves :: T2 (H p) -> (T2 (H p), T2 p)
addThreeHalves T0 = (THalf, THalf)
addThreeHalves THalf = (T1, THalf)
addThreeHalves T1 = (THalf, T1)

restrict :: [a] -> FreeDomain a -> FreeDomain a
restrict xs = (foldr1 glb (map return xs) `lub`)

t2 = restrict [T0, THalf, T1] . return

adder :: T2 (H p) -> T2 (H p) -> T2 (H p) -> (T2 (H p), FreeDomain (T2 p))
-- When x and y add to an integer, we can compute the out carry without
-- looking at the in carry.
adder T0 T0 = (, return T0)
adder T0 T1 = (, return THalf) 
adder THalf THalf = (, return THalf)
adder T1 T0 = (, return THalf)
adder T1 T1 = (, return T1)

adder T0 THalf = fst . addHalf &&& fmap (snd . addHalf) . t2
adder THalf T0 = fst . addHalf &&& fmap (snd . addHalf) . t2
adder THalf T1 = fst . addThreeHalves &&& fmap (snd . addThreeHalves) . t2
adder T1 THalf = fst . addThreeHalves &&& fmap (snd . addThreeHalves) . t2

adder' :: T2 (H p) -> T2 (H p) -> FreeDomain (T2 (H p)) -> (T2 (H p), FreeDomain (T2 p))
adder' x y = runFD . fmap (adder x y)

infixr 9 :>
data Str p = T2 p :> Str (H p)
    deriving (Show)

instance HasGlb (Str p) where
    (x :> xs) `glb` (y :> ys) = (x `glb` y) :> (xs `glb` ys)

instance HasLub (Str p) where
    (x :> xs) `lub` (y :> ys) = (x `lub` y) :> (xs `lub` ys)

adderS :: Str (H p) -> Str (H p) -> (Str (H p), FreeDomain (T2 p))
adderS (x :> xs) (y :> ys) = (xy :> xys, c')
    where
    (xys,c) = adderS xs ys
    (xy,c') = adder' x y c
 

{-
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
-}
