{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}

import Data.Function (fix)
import Data.Foldable (toList)

infixr 6 :+
data Series a = a :+ Series a
    deriving (Show, Functor, Foldable)

x :: (Num a) => Series a
x = 0 :+ 1 :+ fix (0 :+)

zipMulSum :: (Num a) => [a] -> Series a -> a
zipMulSum [] _ = 0
zipMulSum (a:as) (b :+ bs) = (a*b) + zipMulSum as bs

fromList :: (Num a) => [a] -> Series a
fromList [] = fix (0 :+)
fromList (a:as) = a :+ fromList as

lift2 :: (a -> b -> c) -> Series a -> Series b -> Series c
lift2 f (a :+ as) (b :+ bs) = f a b :+ lift2 f as bs

takeS :: Int -> Series a -> [a]
takeS 0 _ = []
takeS n (a :+ as) = a : takeS (n-1) as

dropS :: Int -> Series a -> Series a
dropS 0 s = s
dropS n (a :+ as) = dropS (n-1) as

eval :: (Num a) => Int -> Series a -> a -> a
eval n as z = sum (zipWith (*) (iterate (*z) 1) (takeS n as))

instance (Num a) => Num (Series a) where
    fromInteger a = fromInteger a :+ fix (0 :+)
    (+) = lift2 (+)
    (-) = lift2 (-)
    negate = fmap negate
    (a :+ as) * bs = fmap (a*) bs + (0 :+ as * bs)
    signum = undefined
    abs = undefined

-- Constant term must be 1
integralReciprocal :: (Num a) => Series a -> Series a
integralReciprocal (_ :+ as) = 1 :+ worker [1]
    where
    worker bs = let b' = - zipMulSum bs as
                in b' :+ worker (b':bs)

instance (Fractional a) => Fractional (Series a) where
    -- Constant term must be nonzero.
    recip as@(a :+ _) = fmap (/a) (integralReciprocal (fmap (/a) as))
    fromRational = (:+ 0) . fromRational

deriv :: (Num a) => Series a -> Series a
deriv (a :+ as) = lift2 (*) as (f 1)
    where
    f n = n :+ f (n+1)

integral :: (Fractional a) => a -> Series a -> Series a
integral a0 as = a0 :+ lift2 (/) as (f 1)
    where
    f n = n :+ f (n+1)

-- Constant term of bs must be 0
compose :: (Num a) => Series a -> Series a -> Series a
compose as bs = diag (lift2 (fmap . (*)) as (fromList (iterate (* bs) 1)))
    where
    diag ((a :+ as) :+ ass) = a :+ (as + diag (fmap (dropS 1) ass))

-- Constant term must be 0, linear term must be nonzero.
inverse :: (Fractional a) => Series a -> Series a
-- Derivative of the inverse is the inverse of the derivative.
inverse as = let s = integral 0 (1 / compose (deriv as) s) in s

-- `fixedPoint f` at 1 is a fixed point of f
fixedPoint :: (Num a) => Series a -> Series a
fixedPoint f = let g = 0 :+ (f `compose` g) in g

-- Again, at 1
root :: (Num a) => Series a -> Series a
root f = fixedPoint (f+x)

-- g(x) = x f(g(x))  when x = 1

expS :: (Fractional a) => Series a
expS = go 1 1
    where
    go n a = (1/a) :+ go (n+1) (a*n)

sinS :: (Fractional a) => Series a
sinS = go 0 1
    where
    go n a = 0 :+ (1/((n+1)*a)) :+ go (n+2) (-a*(n+1)*(n+2))

cosS :: (Fractional a) => Series a
cosS = deriv sinS
