{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving #-}

import Data.Complex
import Control.Applicative
import Data.VectorSpace

-- Complexes taken as the scalar field rather than a vector space over R.
newtype C = C { getC :: Complex Double }
    deriving (Eq,Show,Num,Fractional,Floating)

instance AdditiveGroup C where
    C a ^+^ C b = C (a + b)
    zeroV = C 0
    negateV (C x) = C (negate x)

instance VectorSpace C where
    type Scalar C = C
    C x *^ C y = C (x * y)

i :: C
i = C (0 :+ 1)


instance (AdditiveGroup a) => AdditiveGroup [a] where
    [] ^+^ ys = ys
    xs ^+^ [] = xs
    (x:xs) ^+^ (y:ys) = (x ^+^ y) : (xs ^+^ ys)

    zeroV = []

    negateV = map negateV

instance (VectorSpace a) => VectorSpace [a] where
    type Scalar [a] = Scalar a

    (*^) = map . (*^)


euler :: (VectorSpace v) => (v -> v) -> Scalar v -> v -> v
euler d h y = y ^+^ h *^ d y

rk4 :: (VectorSpace v, Fractional (Scalar v)) => (v -> v) -> Scalar v -> v -> v
rk4 d h y = y ^+^ (h/6) *^ (k1 ^+^ 2 *^ k2 ^+^ 2 *^ k3 ^+^ k4)
    where
    k1 = d y
    k2 = d (y ^+^ (h/2) *^ k1)
    k3 = d (y ^+^ (h/2) *^ k2)
    k4 = d (y ^+^ h *^ k3)


-- Integrating with coefficients directly representing a_n
transportd :: (VectorSpace a, Num (Scalar a)) => [a] -> [a]
transportd = go 0
    where
    go n [] = []
    go n [a] = [a]
    go n (a:a':as) = ((n + 1) *^ a') : go (n+1) (a':as)

-- Coefficients representing log a_n
logTransportd :: (Floating a) => [a] -> [a]
logTransportd = go 0
    where
    go n [] = []
    go n [b] = [b]
    go n (b:b':bs) = ((n + 1) * exp (b' - b)) : go (n+1) (b':bs)

-- Coefficients representing a_n/n!
factTransportd :: (VectorSpace a, Num (Scalar a)) => [a] -> [a]
factTransportd = go 0
    where
    go n [] = []
    go n [c] = [c]
    go n (c:c':cs) = ((n + 1)^2 *^ c') : go (n+1) (c':cs)
    

circlePath :: Int -> [C]
circlePath points = [ 1 - exp (pi * i * toC θ) | θ <- [0,recip (fromIntegral points)..1] ]
    where
    pathf θ = exp ((0 :+ 1) * θ) + 1
    toC x = C (x :+ 0)

difference :: (Num a) => [a] -> [a]
difference = liftA2 (zipWith (-)) tail id

scanf :: a -> [a -> a] -> [a]
scanf = scanl (flip ($))

fact n = product [1..n]
