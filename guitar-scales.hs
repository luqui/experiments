import Data.Maybe (catMaybes)

data Position
    = Position { pName :: String, pFrets :: [[Int]], pDegree :: Int }

positions :: [Position]
positions = [
    Position {
        pName = "Phrygian",
        pFrets = parseFrets
            [ "oo-o"
            , "oo-o"
            , "o-o-"
            , "o-oo"
            , "o-oo"
            , "oo-o" ],
        pDegree = 3
    },
    Position {
        pName = "Locrian",
        pFrets = parseFrets
            [ "oo-o"
            , "-o-o"
            , "o-oo"
            , "o-oo"
            , "oo-o"
            , "oo-o" ],
        pDegree = 7
    },
    Position {
        pName = "Dorian",
        pFrets = parseFrets
            [ "-o-oo"
            , "-o-oo"
            , "oo-o"
            , "oo-o"
            , "-o-o-"
            , "-o-oo" ],
        pDegree = 2
    },
    Position {
        pName = "Aeolian",
        pFrets = parseFrets
            [ "-o-oo"
            , "-oo-o"
            , "oo-o-"
            , "-o-o-"
            , "-o-oo"
            , "-o-oo" ],
        pDegree = 6
    },
    Position {
        pName = "Mixolydian",
        pFrets = parseFrets
            [ "-o-o-"
            , "-o-oo"
            , "o-oo-"
            , "oo-o-"
            , "oo-o-"
            , "-o-o-" ],
        pDegree = 5
    }
  ]

parseFrets :: [String] -> [[Int]]
parseFrets = reverse . map parseString
    where
    parseString = 
        catMaybes . 
        zipWith (\fret x -> 
            if x == 'o' then Just fret
                        else Nothing)
        [0..]


{-
--o-o---o--
----o---o--
--o---o-o--
--o---o-o--
--o-o---o--
--o-o---o--
-}

renderPosition :: Position -> [String]
renderPosition pos = reverse . map renderString . pFrets $ pos
    where
    renderString str = concat [ if n `elem` str then "o-" else "--" | n <- [0..maxFret ] ]
    maxFret = maximum . concat $ pFrets pos
