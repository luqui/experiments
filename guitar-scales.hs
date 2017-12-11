{-# LANGUAGE MultiWayIf, TupleSections #-}

import Data.Maybe (catMaybes)
import Control.Arrow (second)
import Control.Monad.Trans.State (state, evalState)

data Position
    = Position { pName :: String, pFrets :: [[(Int,Int)]] }
    -- frets are (fret, degree of major scale)

positions :: [Position]
positions = [
    Position {
        pName = "Phrygian",
        pFrets = parseFrets 3
            [ "oo-o"
            , "oo-o"
            , "o-o-"
            , "o-oo"
            , "o-oo"
            , "oo-o" ]
    },
    Position {
        pName = "Locrian",
        pFrets = parseFrets 7
            [ "oo-o"
            , "-o-o"
            , "o-oo"
            , "o-oo"
            , "oo-o"
            , "oo-o" ]
    },
    Position {
        pName = "Dorian",
        pFrets = parseFrets 2
            [ "-o-oo"
            , "-o-oo"
            , "oo-o"
            , "oo-o"
            , "-o-o-"
            , "-o-oo" ]
    },
    Position {
        pName = "Aeolian",
        pFrets = parseFrets 6
            [ "-o-oo"
            , "-oo-o"
            , "oo-o-"
            , "-o-o-"
            , "-o-oo"
            , "-o-oo" ]
    },
    Position {
        pName = "Mixolydian",
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



