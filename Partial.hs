{-# LANGUAGE RankNTypes, ConstraintKinds #-}

module Partial where

import Control.Applicative
import Control.Monad (ap)
import Control.Arrow (second)
import Data.Lub (HasLub(lub), flatLub)
import Data.Glb (HasGlb(glb), glbs1, flatGlb)
type Domain a = (HasLub a, HasGlb a)

newtype FreeDomain a = FD { getFD :: forall b. Domain b => (a -> b) -> b }

instance Functor FreeDomain where
    fmap f fd = FD $ \c -> getFD fd (c . f)

instance Applicative FreeDomain where
    pure = return
    (<*>) = ap

instance Monad FreeDomain where
    return x = FD $ \c -> c x
    m >>= f = FD $ \c -> getFD m (\x -> getFD (f x) c)

instance HasGlb (FreeDomain a) where
    glb (FD f) (FD g) = FD (f `glb` g)

instance HasLub (FreeDomain a) where
    lub (FD f) (FD g) = FD (f `lub` g)

down :: Int -> Int
down 0 = 0
down 1 = 0
down 2 = 1
down _ = 2




newtype Partial a = Partial { partial :: forall b. Domain b => (a -> b) -> (a -> b) }

values :: [a] -> Partial a
values xs = Partial $ \f -> const (glbs1 (map f xs)) `lub` f

constant :: a -> Partial a
constant x = Partial $ \f -> const (f x)

data Inc a = Inc (Partial a) a

mapInc :: (Domain b) => (a -> b) -> Inc a -> Inc b
mapInc f = unit . apply f

apply :: (Domain b) => (a -> b) -> Inc a -> b
apply f (Inc p x) = partial p f x

domain :: [a] -> a -> Inc a
domain xs x = Inc (values xs) x

restrict :: (Domain a) => [a] -> Inc a -> Inc a
restrict xs = domain xs . counit

unit :: a -> Inc a
unit x = Inc (constant x) x

counit :: (Domain a) => Inc a -> a
counit (Inc p x) = partial p id x

-- costrong?
squeezeR :: (Domain a, Domain b) => Inc (a,b) -> (a, Inc b)
squeezeR = second unit . counit




