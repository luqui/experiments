{-# LANGUAGE RankNTypes, ConstraintKinds #-}

module Partial where

import Control.Applicative
import Control.Monad (ap, liftM)
import Control.Arrow (second)
import Data.Lub (HasLub(lub), flatLub)
import Data.Glb (HasGlb(glb), glbs1, flatGlb)
type Domain a = (HasLub a, HasGlb a)

newtype FreeDomain a = FD { getFD :: forall b. Domain b => (a -> b) -> b }

runFD :: (Domain a) => FreeDomain a -> a
runFD fd = getFD fd id

instance Functor FreeDomain where
    fmap = liftM

instance Applicative FreeDomain where
    pure = return
    (<*>) = ap

instance Monad FreeDomain where
    return x = FD $ \c -> c x
    m >>= f = FD $ \c -> getFD (f undefined) c `lub` getFD m (\x -> getFD (f x) c)

instance HasGlb (FreeDomain a) where
    glb (FD f) (FD g) = FD (f `glb` g)

instance HasLub (FreeDomain a) where
    lub (FD f) (FD g) = FD (f `lub` g)

down :: Int -> Int
down 0 = 0
down 1 = 0
down 2 = 1
down _ = 2

test :: Int
test = runFD $ down.down.down <$> foldr1 glb (map return [1..10])

costrength :: (Domain a) => FreeDomain (a, b) -> (a, FreeDomain b)
costrength fd = (runFD (fmap fst fd), fmap snd fd)
