{-# LANGUAGE TypeApplications, RankNTypes, UnboxedTuples, FlexibleContexts, UndecidableInstances, ScopedTypeVariables #-}

import Data.Monoid
import Unsafe.Coerce
import Data.Reflection
import Data.Proxy

newtype Magic = Magic { getMagic :: forall a. Monoid a => a -> a }

useMonoid :: Monoid a => a -> a
useMonoid x = mconcat [x, x, x, x, x]

-- Looks like the Monoid dictionary is just a tuple of each of its methods. Not even unboxed!
tryThis :: Integer
tryThis = unsafeCoerce (Magic useMonoid) (1, (*), product @[]) 2



-- It is also possible, though more cumbersome, and much safer, to make a
-- typeclass anonymizable, though the values have to be newtyped.
data MonoidDict a = MonoidDict { dmempty :: a, dmappend :: a -> a -> a, dmconcat :: [a] -> a }

newtype AMonoid s a = AMonoid { getAMonoid :: a }

instance (Reifies s (MonoidDict a)) => Monoid (AMonoid s a) where
    mempty = AMonoid $ dmempty (reflect (Proxy @s))
    mappend (AMonoid x) (AMonoid y) = AMonoid $ dmappend (reflect (Proxy @s)) x y
    mconcat = AMonoid . dmconcat (reflect (Proxy @s)) . map getAMonoid

tryThisToo :: Integer
tryThisToo = reify (MonoidDict 1 (*) product) (\(Proxy :: Proxy s) -> getAMonoid (useMonoid (AMonoid @s 2)))
