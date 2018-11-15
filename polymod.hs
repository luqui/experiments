{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving #-}

import Data.Bits
import Data.List (foldl', intercalate)
import GHC.Exts (IsString(..))

newtype Bin = Bin Integer
    deriving (Eq,Ord,Num,Enum,Real,Integral,Bits)

instance Show Bin where
    show (Bin x) = showBin x

instance IsString Bin where
    fromString = readBin

toBits :: (Integral a) => a -> [a]
toBits 0 = []
toBits n = r : toBits d
    where
    (d,r) = n `divMod` 2

showBin :: (Integral a, Show a) => a -> String
showBin = map showb . reverse . toBits
    where
    showb 0 = '0'
    showb 1 = '1'
    showb n = error ("Not a bit: " ++ show n)

readBin :: (Integral a) => String -> a
readBin = go . reverse
    where
    go [] = 0
    go ('0':x) = 2 * go x
    go ('1':x) = 2 * go x + 1
    go (c:x) = error ("Not a bit: " ++ show c)

xmul :: (Integral a, Bits a) => a -> a -> a
xmul x y = foldl' xor 0 $ zipWith (\o b -> o*b*y) (iterate (2*) 1) (toBits x) 

-- (x^2 + 1) (x^3 + x + 1)
-- x^5 + x^3 + x^2
--     + x^3      + x + 1
-- ----------------------
-- x^5       + x^2 + x + 1
--
-- 101 * 1011 = 100111
--

degree :: (Num a, Bits a) => a -> Int
degree x = max 0 $ head [ n | n <- [0..], x `shiftR` n == 0 ] - 1

polymod1 :: (Integral a, Bits a) => a -> a -> a
polymod1 x p = ((x `shiftR` deg) `xmul` (p `clearBit` deg)) `xor` (x .&. (2^deg - 1))
    where
    deg = degree p

polymod :: (Integral a, Bits a) => a -> a -> a
polymod x p = converge $ iterate (`polymod1` p) x
    where
    converge (x:y:xs) | x == y = x
                      | otherwise = converge (y:xs)

multTable :: (Show a, Integral a, Bits a) => a -> Int -> String
multTable modulus pow = unlines $ 
        [ topLine ]
     ++ [ replicate width ' ' ++ " +" ++ replicate (length topLine - width - 2) '-' ]
     ++ [ showW n ++ " | " ++ intercalate " " [ showW ((m `xmul` n) `polymod` modulus) | m <- [0..2^pow-1] ]  | n <- [0..2^pow-1] ]
    where
    width = length . show $ 2^pow - 1
    showW x = replicate (width - length (show x)) ' ' ++ show x
    topLine = replicate width ' ' ++ "   " ++ intercalate " " (map showW [0..2^pow-1]) 

factors :: (Integral a, Bits a) => a -> [a]
factors p = [ d | d <- [1..2^degree p-1], p `polymod` d == 0 ]

isIrreducible :: (Integral a, Bits a) => a -> Bool
isIrreducible p = length (factors p) == 1

{-
Try
>>> putStrLn $ multTable (readBin "111") 2
-}

