{-# Language TypeOperators, RankNTypes, DataKinds, TypeFamilies, PolyKinds, ScopedTypeVariables, ImpredicativeTypes#-}

import Control.Arrow
import Unsafe.Coerce

data Tree a = Leaf a | Branch (Tree (a,a))
    deriving Show

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f (Leaf x) = Leaf (f x)
mapTree f (Branch t) = Branch (mapTree (f *** f) t)


newtype Lim f = Lim { getLim :: forall a. f a }

newtype PolyfixH f a = PolyfixH { getPolyfixH :: (Lim f -> f a) -> Lim f }

polyfixh :: forall f. Lim (PolyfixH f)
polyfixh = Lim (PolyfixH (\f -> 
        let r = Lim (f (getPolyfixH (getLim polyfixh) f)) in r))

polyfix :: forall f a. ((forall x. f x) -> f a) -> f a
polyfix f = getLim (getPolyfixH (getLim polyfixh) (\limf -> f (getLim limf)))

data a * b = Pair a b

type family Proj1 p where
    Proj1 (Pair a b) = a
type family Proj2 p where
    Proj2 (Pair a b) = b

newtype MapTree p = MapTree { getMapTree :: (Proj1 p -> Proj2 p) -> Tree (Proj1 p) -> Tree (Proj2 p) }

mapTree' :: (a -> b) -> Tree a -> Tree b
mapTree' = getMapTree final
    where
    final :: MapTree (Pair a b)
    final = polyfix (\(rec :: MapTree (Pair (a,a) (b,b))) -> MapTree (\f t -> 
        case t of
            Leaf x -> Leaf (f x)
            Branch t -> Branch (getMapTree rec (f *** f) t)
        ) :: MapTree (Pair a b)
      )
