{-# LANGUAGE DeriveFunctor, TupleSections, FlexibleContexts #-}

import Control.Applicative hiding (empty)
import Control.Concurrent (threadDelay, forkIO)
import Control.Monad (replicateM, replicateM_, forever, join, forM_, filterM)
import Data.IORef
import Data.Monoid
import qualified Data.Map as Map
import qualified System.MIDI as MIDI
import qualified Control.Monad.Random as Rand

class GenRandom a where
    genRandom :: (Rand.RandomGen g) => Rand.Rand g a

class Enumerate a where
    enumerate :: [a]

class Empty a where
    empty :: a
instance (Empty b) => Empty (a -> b) where
    empty _ = empty
instance Empty [a] where
    empty = []

data Nonterm = S Char
    deriving (Eq, Ord, Show)
instance Enumerate Nonterm where
    enumerate = map S ['A'..'Z']
instance GenRandom Nonterm where
    genRandom = Rand.uniform enumerate

newtype Note = N Int
    deriving (Show)
instance GenRandom Note where
    genRandom = N <$> Rand.uniform [0..7]

newtype Vel = V Double
    deriving (Show)
instance GenRandom Vel where
    genRandom = V <$> Rand.getRandomR (0,1)


data BeatF a
    = Rest
    | Note Note Vel
    | Concat [a]
    | Parallel [a]
    deriving (Show, Functor)

instance Empty (BeatF a) where
    empty = Rest

instance (GenRandom a) => GenRandom (BeatF a) where
    genRandom = join $ Rand.uniform [
        pure Rest,
        Note <$> genRandom <*> genRandom,
        Rand.getRandomR (2,4) >>= \n -> Concat <$> replicateM n genRandom,
        Parallel <$> replicateM 2 genRandom
      ]

evalBeatF :: BeatF (Double -> RawBeat) -> Double -> RawBeat
evalBeatF Rest sz = [RawRest sz]
evalBeatF (Note n v) sz = [RawNote n v, RawRest sz]
evalBeatF (Concat xs) sz = concatMap ($ sz / len) xs
    where
    len = fromIntegral (length xs)
evalBeatF (Parallel xs) sz = foldr par [] (map ($ sz) xs)

data IFS f a = IFS a (Map.Map a (f a))
    deriving Show

instance (GenRandom (f a), GenRandom a, Enumerate a, Ord a) => GenRandom (IFS f a) where
    genRandom = IFS <$> genRandom <*> (Map.fromList <$> elems)
        where
        elems = mapM (\e -> (e,) <$> genRandom) enumerate

fuseN :: (Functor f, Empty b) => Int -> (f b -> b) -> (a -> f a) -> (a -> b)
fuseN 0 _ _ = const empty
fuseN n alg coalg = alg . fmap (fuseN (n-1) alg coalg) . coalg

expandIFSN :: (Ord a, Functor f, Empty b) => Int -> (f b -> b) -> IFS f a -> b
expandIFSN n alg (IFS start m) = fuseN n alg (m Map.!) start

printIFS :: (Show a, Show (f a), Enumerate a, Ord a) => IFS f a -> IO ()
printIFS (IFS start m) = do
    forM_ enumerate $ \a -> putStrLn $ show a ++ " -> " ++ show (m Map.! a)
    putStrLn $ "start = " ++ show start

evolveKernel :: (a -> a -> Rand.Rand Rand.StdGen a) -> (a -> Rand.Rand Rand.StdGen a) -> 
                (a -> IO ()) -> [a] -> IO ()
evolveKernel sex mutate shower pool = do
    let poolsize = length pool
    newpool <- flip filterM pool $ \l -> do
        shower l
        putStr $ "Good? "
        answer <- getLine 
        return $ answer == "y"
    newelems <- Rand.evalRandIO . replicateM (poolsize - length newpool) $ do
        boy <- Rand.uniform newpool
        girl <- Rand.uniform newpool
        sex boy girl
    putStrLn "------------------------"
    putStrLn "A NEW GENERATION IS BORN"
    putStrLn "------------------------"
    newelems' <- Rand.evalRandIO $ mapM mutate (newelems ++ newpool)
    evolveKernel sex mutate shower newelems'

ifsSex :: (Rand.RandomGen g, Ord a, Enumerate a) => IFS f a -> IFS f a -> Rand.Rand g (IFS f a)
ifsSex (IFS boystart boy) (IFS girlstart girl) = do
    newmap <- Map.fromList <$> mapM (\a -> (a,) <$> Rand.uniform [boy Map.! a, girl Map.! a]) enumerate
    IFS <$> Rand.uniform [boystart, girlstart] <*> pure newmap

ifsShow :: (RawBeat -> IO ()) -> IFS BeatF Nonterm -> IO ()
ifsShow beat ifs = do
    printIFS ifs
    let expanded = expandIFSN 5 evalBeatF ifs 2
    print expanded
    beat expanded

ifsMutate :: (GenRandom a, GenRandom (f a), Ord a, Rand.RandomGen g) => IFS f a -> Rand.Rand g (IFS f a) 
ifsMutate (IFS start rules) = do
    cancer <- genRandom
    target <- genRandom
    return $ IFS start (Map.insert cancer target rules)

initialPool :: Int -> IO [IFS BeatF Nonterm]
initialPool 0 = return []
initialPool size = do
    ifs <- Rand.evalRandIO genRandom :: IO (IFS BeatF Nonterm)
    let expanded = expandIFSN 5 evalBeatF ifs 2
    if length expanded > 4 then do
        (ifs :) <$> initialPool (size-1)
    else
        initialPool size


data RawItem = RawRest Double | RawNote Note Vel
    deriving (Show)
type RawBeat = [RawItem]

(+:) :: RawItem -> RawBeat -> RawBeat
RawRest r +: [] = [RawRest r]
RawRest r +: (RawRest r' : bs) = RawRest (r+r') : bs
RawRest r +: (RawNote n v : bs) = RawRest r : RawNote n v : bs
RawNote n v +: bs = RawNote n v : bs

par :: RawBeat -> RawBeat -> RawBeat
par [] bs = bs
par as [] = as
par (RawNote n v:as) bs = RawNote n v +: par as bs
par as (RawNote n v:bs) = RawNote n v +: par as bs
par (RawRest r:as) (RawRest r':bs)
    | r <= r' = RawRest r +: par as (RawRest (r'-r):bs)
    | otherwise = RawRest r' +: par (RawRest (r-r'):as) bs

midiVel :: Vel -> Int
midiVel (V v) = max 0 . min 127 $ floor (127*v)

midiNote :: Note -> Int
midiNote (N i)  
    | i < 8 = [60,62,64,65,67,69,71,72] !! i
    | otherwise = 0

playNote :: MIDI.Connection -> Note -> Vel -> IO ()
playNote conn n v = do
    MIDI.send conn (MIDI.MidiMessage 1 (MIDI.NoteOn (midiNote n) (midiVel v)))
    MIDI.send conn (MIDI.MidiMessage 1 (MIDI.NoteOn (midiNote n) 0))

delay :: Double -> IO ()
delay sec = threadDelay (floor (10^6 * sec))

interp :: MIDI.Connection -> RawBeat -> IO ()
interp conn = mapM_ interp1
    where
    interp1 (RawRest r) = delay r
    interp1 (RawNote n v) = playNote conn n v

mkPlayer :: IO (RawBeat -> IO ())
mkPlayer = do
    conn <- MIDI.openDestination =<< head <$> MIDI.enumerateDestinations
    ref <- newIORef [RawRest 1]
    _ <- forkIO . forever $ do
        beat <- readIORef ref
        if null beat then delay 1 else interp conn beat
    return $ writeIORef ref
