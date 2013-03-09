{-# LANGUAGE RankNTypes #-}

module Natural where

import Data.Traversable
import Control.Monad.Trans.State

data Labelled a = Labelled { label :: Integer, value :: a }

instance Eq (Labelled a) where
    a == b = compare a b == EQ

instance Ord (Labelled a) where
    compare a b = compare (label a) (label b)


labels :: (Traversable t) => t a -> t (Labelled a)
labels t = evalState (traverse trav t) 0
    where
    trav x = state (\i -> i `seq` (Labelled i x, i + 1))

onIndices :: (Traversable t, Functor u) 
          => (forall a. Ord a => t a -> u a) 
          -> forall b. t b -> u b
onIndices f = fmap value . f . labels
