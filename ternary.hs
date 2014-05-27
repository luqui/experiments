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

addS :: Str (H p) -> Str (H p) -> Str p
addS x y = runFD c :> xy
    where
    (xy,c) = adderS x y


data Ref p = Ref {
    toApprox :: Str p -> (Rational -> Rational),
    fromApprox :: (Rational -> Rational) -> Str p
}

normalizeApprox :: (Rational, Rational) -> (Rational -> Rational) -> (Rational -> Rational)
normalizeApprox (lo,hi) f = (/ (hi-lo)) . subtract lo . f . (* (hi-lo))

renderApprox :: (Rational, Rational) -> (Rational -> Rational) -> (Rational -> Rational)
renderApprox (lo,hi) f = (+lo) . (* (hi-lo))  . f . (/ (hi-lo))

withRef :: (Rational, Rational) -> (forall p. Ref p -> z) -> z
withRef r cont = cont (Ref (renderApprox r . toApprox) (fromApprox . normalizeApprox r))
    where
    toApprox :: Str p -> (Rational -> Rational)
    toApprox s thresh = go (1/2) s
        where
        go :: Rational -> Str p -> Rational
        go err _ | 2*err < thresh = 0
        go err (x :> xs) = err * t2Value x + go (err/2) xs
        
        t2Value :: T2 p -> Rational
        t2Value T0 = 0
        t2Value THalf = 1/2
        t2Value T1 = 1
        

    fromApprox :: (Rational -> Rational) -> Str p
    fromApprox f
        | r <= 1/4 = T0 :> cont 0
        | r >= 3/4 = T1 :> cont (1/2)
        | otherwise = THalf :> cont (1/4)
        where
        r = f (1/4)
        cont s = fromApprox (\q -> 2*(f (q/2) - s))
