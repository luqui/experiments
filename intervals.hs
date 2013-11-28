import Csound
import Data.Ratio
import Data.List

instr n = return $ 0.1 * osc (sig n) 

rscale :: [[D]] -> Score D
rscale = mel . map (har . map (temp.(*440)))

quarterTone = take 25 $ map (:[]) $ iterate (* (2**(1/24))) 1

major :: (Fractional a) => [a]
major = [1,9/8,5/4,4/3,3/2,5/3,15/8]

go = dac $ mix $ sco instr $ rscale $ quarterTone



phi :: (Floating a) => a
phi = (1+sqrt 5)/2

equal n = 2**(n/12)

cdiff a b = 1200 * (log b - log a) / log 2


toEqual :: (Floating a) => a -> a
toEqual x = log x / log (2**(1/12))




{-
Root:    1   :   0
P2:     9/8  : 2+3c
Fourth: 4/3  : 5-2c
Fifth:  3/2  : 7+2c

Major: 
    Maj3:  5/4  : 4-13c
    Maj6:  5/3  : 9-15c
    Dom7:  7/4  : 9.5+18c   ***
    Maj7:  15/8 : 11-11c

Minor:
    Min3:   6/5 : 3+15c
    Min6:   8/5 : 8+13c
    Min7:   9/5 : 10+17c

Neutral: 
    N3:     11/9  : 3.5-2c   (distance from 1 to N3)
            27/22 : 3.5+4c   (distance from N3 to 5) 
    N6:     18/11 : 8.5+3c
    N7:     11/6  : 10.5-1c   (11/9 + fifth)
            81/44 : 10.5+6c  (27/22 + fifth)

-------------------------------------------------------------------------
Major intervals (maj3, maj6, dom7, maj7) are a little smaller than equal
         (dom7 is is closer to 3/4 flat from the major scale)
Minor intervals (min3, min6, min7) are a little bigger than equal
Perfect & neutral intervals are pretty much spot-on
-------------------------------------------------------------------------

Tritone (maj3 & dom7): 7/5 : 6-17c

Diminshed second -- complement to maj Maj7
        16/15 : 1+12c
"Neutral" second -- complement to N7
        12/11 : 1.5+1c
"Minor" second -- complement to min dom7
        10/9 : 2-17c
"Major" second -- complement to maj dom7
        8/7  : 2.5-18c
"Mindom" third -- fifth down from dom7
        7/6 : 2.5+17c


Modes:

Ionian: 1    9/8   5/4    4/3   3/2   5/3    15/8    2
        0    2+3c  4-14c  5-2c  7+2c  9-16c  11-12c  12

Dorian: 1    10/9    32/27  4/3   40/27   5/3    16/9    2
        0    2-18c   3-6c   5-2c  7-20c   9-16c  10-4c   12

Phrygian: 1    16/15   6/5    4/3   3/2   8/5    9/5     2
          0    1+11c   3+15c  5-2c  7+2c  8+13c  10+17c  12

Lydian:  1    9/8   5/4    45/32   3/2   27/16   15/8    2
         0    2+3c  4-14c  6-10c   7+2c  9+6c    11-12c  12

Mixolydian: 1    10/9   5/4    4/3   3/2   5/3   16/9    2
            0    2-18c  4-14c  5-2c  7+2c  9-16c 10-4c   12

Aeolian:  1    9/8    6/5    27/20   3/2    8/5    9/5    2
          0    2+3c   3+16c  5+20c   7+2c   8+14c  10+18c 12

Locrian:  1    16/15  6/5    4/3     64/45   8/5    16/9   2
          0    1+11c  3+16c  5-2c    6+10c   8+14c  10-4c  12
-}
