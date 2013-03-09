import qualified Data.MemoCombinators as Memo
import Test.QuickCheck
import Debug.Trace
import System.Environment (getArgs)

binarySearch :: (Integer -> Ordering) -> Integer
binarySearch p = find 1 (grow 1)
    where
    --grow n | trace ("grow " ++ show n) False = undefined
    grow n | p n == GT = grow (2*n)
           | otherwise = n
    --find m n | trace ("find " ++ show m ++ " " ++ show n) False = undefined
    find m n | m == n = m
    find m n =
        case p c of
            LT -> find m (c-1)
            EQ -> c
            GT -> find c n
        where
        c = (m + n) `cdiv` 2

cdiv m n = -((-m) `div` n)

prop_binarySearch n = n >= 1 ==> binarySearch (n `compare`) == n
                
dlog2 :: Integer -> Integer
dlog2 n = binarySearch (\m -> n `compare` (2^m))

prop_dlog2 n = n >= 2 ==> 2^d <= n && n < 2^(d+1)
    where
    d = dlog2 n

sx = Memo.integral go
    where
    go 1 = 1
    go n = sum [ sx k^2 | k <- [1..n-1] ]

main = do
    mapM_ (print . dlog2 . dlog2 . sx) [1..]
