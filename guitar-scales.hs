{-# LANGUAGE MultiWayIf, TupleSections #-}

import Data.Maybe (catMaybes)
import Control.Applicative (liftA2)
import Control.Arrow (second)
import Control.Monad (forever, forM_)
import Control.Monad.Trans.State (state, evalState)
import System.IO (hFlush, stdout)
import qualified Control.Monad.Random as Rand

data Position
    = Position { pName :: String, pFrets :: [[(Int,Int)]] }
    -- frets are (fret, degree of major scale)

positions :: [Position]
positions = [
    Position {
        pName = "phr",
        pFrets = parseFrets 3
            [ "oo-o"
            , "oo-o"
            , "o-o-"
            , "o-oo"
            , "o-oo"
            , "oo-o" ]
    },
    Position {
        pName = "loc",
        pFrets = parseFrets 7
            [ "oo-o"
            , "-o-o"
            , "o-oo"
            , "o-oo"
            , "oo-o"
            , "oo-o" ]
    },
    Position {
        pName = "dor",
        pFrets = parseFrets 2
            [ "-o-oo"
            , "-o-oo"
            , "oo-o"
            , "oo-o"
            , "-o-o-"
            , "-o-oo" ]
    },
    Position {
        pName = "aeo",
        pFrets = parseFrets 6
            [ "-o-oo"
            , "-oo-o"
            , "oo-o-"
            , "-o-o-"
            , "-o-oo"
            , "-o-oo" ]
    },
    Position {
        pName = "mix",
        pFrets = parseFrets 5
            [ "-o-o-"
            , "-o-oo"
            , "o-oo-"
            , "oo-o-"
            , "oo-o-"
            , "-o-o-" ]
    }
  ]

parseFrets :: Int -> [String] -> [[(Int,Int)]]
parseFrets degree = annotate . reverse . map parseString
    where
    parseString = 
        catMaybes . 
        zipWith (\fret x -> 
            if x == 'o' then Just fret
                        else Nothing)
        [0..]
    annotate = flip evalState degree .
                (traverse.traverse) (\n -> (n,) <$> inc)
    inc = state $ \i -> (i, (i `mod` 7) + 1)


renderPosition :: Maybe Int -> [[(Int,Int)]] -> [String]
renderPosition highlight frets = reverse . map renderString $ frets
    where
    renderString str = concat [ 
        if | (n,highlight) `elem` map (second Just) str -> "X-"
           | n `elem` map fst str -> "o-" 
           | otherwise -> "--"
        | n <- [0..maxFret ] ]
    maxFret = maximum . map fst . concat $ frets

padRender :: Int -> Int -> [String] -> [String]
padRender pre post = map ((dashes pre ++) . (++ dashes post))
    where
    dashes n = replicate (2*n) '-'

patternGame :: [Int] -> IO ()
patternGame strings = do
    pos <- Rand.evalRandIO $ Rand.uniform positions
    let question = do
            mapM_ putStrLn $ zipWith (++) (map show strings) (padRender 1 1 $ renderPosition Nothing (reverse $ map ((pFrets pos !!) . (6-)) strings))
            putStr $ "Pattern? "
            answer <- getLine
            if answer == pName pos
                then putStrLn "\ESC[1;32mYep!\ESC[0m"
                else putStrLn "\ESC[1;31mNope!\ESC[0m" >> question
    question

randPatternGame :: IO ()
randPatternGame = do
    strings <- Rand.evalRandIO $ Rand.uniform [[1,2],[3,4],[5,6],[1,2,3],[4,5,6],[1,2,3,4,5,6]]
    patternGame strings


degreeGame :: [Int] -> IO ()
degreeGame strings = do
    (pos,deg) <- Rand.evalRandIO $ liftA2 (,) (Rand.uniform positions) (Rand.uniform [1..7])
    let question = do
            mapM_ putStrLn $ zipWith (++) (map show strings) (padRender 1 1 $ renderPosition (Just deg) (reverse $ map ((pFrets pos !!) . (6-)) strings))
            putStr $ "Degree of major? "
            hFlush stdout
            answer <- readLn
            if answer == deg
                then putStrLn "\ESC[1;32mYep!\ESC[0m"
                else putStrLn "\ESC[1;31mNope!\ESC[0m" >> question
    question

randDegreeGame :: IO ()
randDegreeGame = do
    strings <- Rand.evalRandIO $ Rand.uniform [[1,2],[3,4],[5,6],[1,2,3],[4,5,6],[1,2,3,4,5,6]]
    degreeGame strings

