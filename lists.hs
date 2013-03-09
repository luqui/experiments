{-# LANGUAGE RankNTypes, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

import Data.List (permutations, nubBy, nub, sort)
import Test.QuickCheck
import Natural (onIndices)
import Data.Foldable
import Data.Traversable

type Partition a = ([a],[a])

canon :: (Ord a) => Partition a -> [[a]]
canon (xs,ys) = sort [sort xs, sort ys]

equiv :: (Ord a) => Partition a -> Partition a -> Bool
equiv p q = canon p == canon q

partitions :: [a] -> [([a],[a])]
partitions xs = map (splitAt l) (permutations xs)
    where
    l = length xs `div` 2

equivPartitions :: (Ord a) => [a] -> [Partition a]
equivPartitions = nubBy equiv . partitions

-- not to be exported
splitLen :: Int -> Int -> [a] -> [([a],[a])]
splitLen 0 _ xs = [([],xs)]
splitLen _ _ [] = error "Oops"
splitLen k l ys@(x:xs)
    | k == l    = [(ys,[])]
    | otherwise = [(x:us,vs) | (us,vs) <- splitLen (k-1) (l-1) xs]
                  ++ [(us,x:vs) | (us,vs) <- splitLen k (l-1) xs]

partitions' :: [a] -> [([a],[a])]
partitions' [] = [([],[])]
partitions' (x:xs)
    | even len  = error "Original list with odd length"
    | otherwise = [(x:us,vs) | (us,vs) <- splitLen half len xs]
      where
        len = length xs
        half = len `quot` 2

newtype PartitionList a = PartitionList {getPartitionList :: [Partition a]}
    deriving (Functor, Foldable, Traversable)

partitions'' :: [a] -> [([a],[a])]
partitions'' = getPartitionList . onIndices (PartitionList . equivPartitions)

prop_equiv xs = even (length xs) ==> (nub (sort (map canon (equivPartitions xs)))
                                   == nub (sort (map canon (partitions' xs))))
    where
    types = xs :: [Int]
