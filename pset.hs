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

main = defaultMain [
    bgroup "pset" [
        bench "list" $ nf pset [1..20::Int],
        bench "list (no share)" $ nf psetNoShare [1..20::Int],
        bench "dlist" $ nf psetDL [1..20::Int],
        bench "dlist (no share)" $ nf psetDL [1..20::Int]
    ]
  ]

{-
$ ghc --make -O pset

benchmarking pset/list
time                 397.0 ms   (326.9 ms .. 444.0 ms)
                     0.997 R²   (0.989 R² .. 1.000 R²)
mean                 425.9 ms   (423.5 ms .. 430.4 ms)
std dev              3.859 ms   (0.0 s .. 3.948 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/list (no share)
time                 1.307 s    (1.282 s .. 1.327 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 1.315 s    (1.309 s .. 1.319 s)
std dev              6.834 ms   (0.0 s .. 7.744 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/dlist
time                 379.8 ms   (327.2 ms .. 441.1 ms)
                     0.997 R²   (0.989 R² .. 1.000 R²)
mean                 382.6 ms   (373.2 ms .. 390.1 ms)
std dev              11.81 ms   (0.0 s .. 13.07 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking pset/dlist (no share)
time                 388.2 ms   (338.6 ms .. 416.7 ms)
                     0.998 R²   (0.995 R² .. 1.000 R²)
mean                 381.1 ms   (369.4 ms .. 387.6 ms)
std dev              10.34 ms   (0.0 s .. 11.23 ms)
variance introduced by outliers: 19% (moderately inflated)
-}
