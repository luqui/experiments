{-# LANGUAGE MultiWayIf, TupleSections #-}

import Data.Maybe (catMaybes)
import Control.Applicative (liftA2)
import Control.Arrow (second)
import Control.Monad (forever, forM_, filterM)
import Control.Monad.Trans.State (state, evalState)
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)
import qualified Control.Monad.Random as Rand

type Cloud = Rand.Rand Rand.StdGen

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

data Mode = Mode
    { modeName :: String
    , modeTransform :: Int -> Int
    }

modeMap :: [Mode]
modeMap =
    [ Mode "major" id
    , Mode "minor" (mode 6)
    , Mode "dorian" (mode 2)
    ]
    where
    mode n d = (((d-1)+(n-1)) `mod` 7) + 1

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

subfretboards :: [[Int]]
subfretboards = [ [x..y] | x <- [1..5], y <- [x+1..6] ]

filterPosition :: [[a]] -> Cloud [[a]]
filterPosition = (traverse.filterM) (const (Rand.uniform [False,True]))

randPatternGame :: IO ()
randPatternGame = do
    strings <- Rand.evalRandIO $ Rand.uniform subfretboards
    patternGame strings


degreeGame :: Mode -> [Int] -> IO ()
degreeGame mode strings = do
    (pos,deg) <- Rand.evalRandIO $ liftA2 (,) (Rand.uniform positions) (Rand.uniform [1..7])
    let question = do
            mapM_ putStrLn $ zipWith (++) (map show strings) (padRender 1 1 $ renderPosition (Just deg) (reverse $ map ((pFrets pos !!) . (6-)) strings))
            putStr $ "Degree of " ++ modeName mode ++ "? "
            hFlush stdout
            answer <- readMaybe <$> getLine
            if (modeTransform mode <$> answer) == Just deg
                then putStrLn "\ESC[1;32mYep!\ESC[0m"
                else putStrLn "\ESC[1;31mNope!\ESC[0m" >> question
    question

randDegreeGame :: IO ()
randDegreeGame = do
    strings <- Rand.evalRandIO $ Rand.uniform subfretboards
    mode <- Rand.evalRandIO $ Rand.uniform modeMap
    degreeGame mode strings


fragmentGame :: [Int] -> IO ()
fragmentGame strings = do
    pos <- Rand.evalRandIO $ Rand.uniform positions
    pos' <- Rand.evalRandIO . filterPosition . reverse . map ((pFrets pos !!) . (6-)) $ strings
    (paddingL, paddingR) <- liftA2 (,) (Rand.uniform [0..2]) (Rand.uniform [0..2])
    let question = do
            mapM_ putStrLn $ zipWith (++) (map show strings) (padRender paddingL paddingR $ renderPosition Nothing pos')
            putStr $ "Pattern? "
            answer <- getLine
            if answer == pName pos
                then putStrLn "\ESC[1;32mYep!\ESC[0m"
                else putStrLn "\ESC[1;31mNope!\ESC[0m" >> question
    question

fullFragmentGame :: IO ()
fullFragmentGame = fragmentGame [1..6]


main = forever randDegreeGame
