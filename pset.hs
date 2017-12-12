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
        bench "tail" $ nf psetTail [1..20::Int],
        bench "tail dlist" $ nf psetTailDL [1..20::Int]
    ]
  ]

{-
$ ghc --make -O pset
time                 417.2 ms   (352.5 ms .. 484.1 ms)
                     0.997 R²   (0.988 R² .. 1.000 R²)
mean                 440.1 ms   (433.7 ms .. 445.7 ms)
std dev              9.097 ms   (67.65 as .. 9.698 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/list (no share)
time                 1.362 s    (1.346 s .. 1.370 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 1.366 s    (1.362 s .. 1.368 s)
std dev              2.965 ms   (0.0 s .. 3.105 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/dlist
time                 392.7 ms   (364.1 ms .. 419.6 ms)
                     0.999 R²   (NaN R² .. 1.000 R²)
mean                 395.3 ms   (389.9 ms .. 398.6 ms)
std dev              5.017 ms   (0.0 s .. 5.723 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/dlist (no share)
time                 423.1 ms   (349.1 ms .. 502.1 ms)
                     0.996 R²   (0.984 R² .. 1.000 R²)
mean                 408.5 ms   (385.3 ms .. 421.5 ms)
std dev              20.55 ms   (69.39 as .. 22.48 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/tail
time                 188.3 ms   (176.6 ms .. 200.3 ms)
                     0.998 R²   (0.995 R² .. 1.000 R²)
mean                 191.0 ms   (186.5 ms .. 194.9 ms)
std dev              5.539 ms   (3.124 ms .. 8.078 ms)
variance introduced by outliers: 14% (moderately inflated)

benchmarking pset/tail dlist
time                 155.2 ms   (151.7 ms .. 158.5 ms)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 153.0 ms   (151.3 ms .. 154.2 ms)
std dev              1.950 ms   (1.211 ms .. 2.811 ms)
variance introduced by outliers: 12% (moderately inflated)
-}
