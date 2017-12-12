import Control.Arrow (first,second)
import Data.Monoid ((<>))
import Data.Foldable (toList)
import qualified Data.DList as DList
import Criterion.Main

pset :: [a] -> [([a],[a])]
pset [] = [([],[])]
pset (x:xs) = (second (x:) <$> rec) <> (first (x:) <$> rec)
    where
    rec = pset xs

psetDL :: [a] -> [([a],[a])]
psetDL = toList . go
    where
    go [] = DList.singleton ([],[])
    go (x:xs) = (second (x:) <$> rec) <> (first (x:) <$> rec)
        where
        rec = go xs

psetNoShare :: [a] -> [([a],[a])]
psetNoShare [] = [([],[])]
psetNoShare (x:xs) = (second (x:) <$> psetNoShare xs) <> (first (x:) <$> psetNoShare xs)

psetDLNoShare :: [a] -> [([a],[a])]
psetDLNoShare = toList . go
    where
    go [] = DList.singleton ([],[])
    go (x:xs) = (second (x:) <$> go xs) <> (first (x:) <$> go xs)

psetTail :: [a] -> [([a],[a])]
psetTail = go [] []
    where
    go a b [] = [(a,b)]
    go a b (x:xs) = go a (x:b) xs <> go (x:a) b xs

psetTailDL :: [a] -> [([a],[a])]
psetTailDL = toList . go [] []
    where
    go a b [] = DList.singleton (a,b)
    go a b (x:xs) = go a (x:b) xs <> go (x:a) b xs

main = defaultMain [
    bgroup "pset" [
        bench "list" $ nf pset [1..20::Int],
        bench "list (no share)" $ nf psetNoShare [1..20::Int],
        bench "dlist" $ nf psetDL [1..20::Int],
        bench "dlist (no share)" $ nf psetDL [1..20::Int],
        bench "tail" $ nf psetDL [1..20::Int],
        bench "tail dlist" $ nf psetDL [1..20::Int]
    ]
  ]

{-
$ ghc --make -O pset

benchmarking pset/list
time                 413.5 ms   (338.1 ms .. 455.8 ms)
                     0.996 R²   (0.992 R² .. 1.000 R²)
mean                 440.8 ms   (439.3 ms .. 442.2 ms)
std dev              2.254 ms   (0.0 s .. 2.385 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/list (no share)
time                 1.421 s    (1.372 s .. 1.466 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 1.389 s    (1.370 s .. 1.401 s)
std dev              18.81 ms   (0.0 s .. 21.72 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/dlist
time                 420.8 ms   (358.8 ms .. 478.1 ms)
                     0.997 R²   (0.990 R² .. 1.000 R²)
mean                 419.1 ms   (404.6 ms .. 427.2 ms)
std dev              12.81 ms   (0.0 s .. 14.13 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/dlist (no share)
time                 401.7 ms   (NaN s .. 410.2 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 412.8 ms   (409.0 ms .. 415.0 ms)
std dev              3.399 ms   (0.0 s .. 3.795 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/tail
time                 380.9 ms   (362.7 ms .. 397.7 ms)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 394.4 ms   (388.7 ms .. 397.3 ms)
std dev              4.947 ms   (0.0 s .. 4.996 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/tail dlist
time                 385.3 ms   (NaN s .. 413.5 ms)
                     0.999 R²   (0.996 R² .. 1.000 R²)
mean                 391.3 ms   (385.6 ms .. 394.4 ms)
std dev              5.001 ms   (0.0 s .. 5.374 ms)
variance introduced by outliers: 19% (moderately inflated)
-}
