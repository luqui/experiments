{-# LANGUAGE BangPatterns #-}

-- Declick a (mono, 32bit only supported now, easy to modify though) wave file that has
-- clipped due to integer overflow.  This turns out to be pretty easy to recover from by 
-- unwrapping the overflow whenever there are large jumps.  At least it works well for my
-- keyboard tracks, it's possible drums will not be so easy. 

import Data.WAVE
import System.IO
import System.Environment
import Data.Int
import System.IO.Unsafe (unsafeInterleaveIO)

toReal :: Int32 -> Double
toReal i = fromIntegral i / fromIntegral (maxBound :: Int32)

declick :: [Double] -> [Double]
declick [] = []
declick (x0:xs) = x0 : go 0 x0 xs
    where
    go shift prev [] = []
    go shift prev (x:xs)
        | x < prev-1 = (x + shift+2) : go (shift+2) x xs
        | x > prev+1 = (x + shift-2) : go (shift-2) x xs
        | otherwise = (x + shift) : go shift x xs

minMax :: (Ord a) => [a] -> (a, a)
minMax [] = error "minMax: empty list"
minMax (x:xs) = go x x xs
    where
    go !lo !hi [] = (lo, hi)
    go !lo !hi (!x:xs)
        | x < lo = go x hi xs
        | x > hi = go lo x xs
        | otherwise = go lo hi xs

normalize :: [Double] -> [Double]
normalize xs = map (/ l) xs
    where
    (lo, hi) = minMax xs
    l = max hi (-lo)

normConstant :: [Double] -> Double
normConstant xs = 1 / max hi (-lo)
    where
    (lo, hi) = minMax xs

fromReal :: Double -> Int32
fromReal x = floor (x * fromIntegral (maxBound :: Int32))

main = do
    [infile, outfile] <- getArgs
    -- load twice to keep working memory free
    wave <- getWAVEFile infile
    putStrLn "Computing normalization constant"
    let !normC = normConstant . declick . map (toReal . head) . waveSamples $ wave
    putStrLn $ "Normalization constant = " ++ show normC
    wave' <- getWAVEFile infile
    putStrLn $ "Declicking & exporting"
    let wavedata' = map ((:[]) . fromReal) . map (* normC) . declick . map (toReal . head) . waveSamples $ wave'
    putWAVEFile outfile (wave { waveSamples = wavedata' })
