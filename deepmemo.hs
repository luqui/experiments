{-# LANGUAGE RankNTypes, LambdaCase #-}

import qualified Data.MemoCombinators as Memo
import Data.Function (fix)
import Debug.Trace (trace)


-- Shallow memoization takes no advantage of the structure of the computation
-- or domain.  fibShallow 30 will take quite a while to compute once and remember
-- that, but fib 31 will still take a long time.
fibShallow :: Integer -> Integer
fibShallow = Memo.integral go
    where
    go 0 = 0
    go 1 = 1
    go n = go (n-1) + go (n-2) 


-- Deep memoization takes advantage of the recursive structure of the
-- computation by opening the fixpoint and memoizing in between.  Once fibDeep
-- 29 and fibDeep 30 are computed, fibDeep31 is trivial.  fibDeep is *much*
-- faster than fibShallow even on first computation.
fibDeep :: Integer -> Integer
fibDeep = Memo.integral go
    where
    go 0 = 0
    go 1 = 1
    go n = fibDeep (n-1) + fibDeep (n-2)

-- This is "bottom-up" deep memoization. It might be summarized as follows:

deepMemo :: Memo.Memo a -> ((a -> r) -> (a -> r)) -> (a -> r)
deepMemo m f = fix (m . f)

fibDeep' :: Integer -> Integer
fibDeep' = deepMemo Memo.integral $ \f -> 
    \case 0 -> 0
          1 -> 1
          n -> f (n-1) + f (n-2)


-- What about "top-down" deep memoization? Consider:

expensiveP :: Int -> Bool
expensiveP x = trace ("expensiveP " ++ show x) (even x)

memoFilter :: Memo.Memo a -> (a -> Bool) -> [a] -> [a]
memoFilter m p = \case [] -> []
                       (x:xs) -> mgo x xs
    where
    mgo = m go
    go x | p x       = (x:) . memoFilter m (not.p)
         | otherwise = memoFilter m p

testMemoFilter :: [Int] -> [Int]
testMemoFilter = memoFilter Memo.integral expensiveP
