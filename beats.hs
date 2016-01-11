import Control.Applicative
import Control.Concurrent (threadDelay, forkIO)
import Control.Monad (replicateM, replicateM_, forever, join)
import Data.IORef
import Data.Monoid
import qualified System.MIDI as MIDI
import qualified Control.Monad.Random as Rand

class GenRandom a where
    genRandom :: (Rand.RandomGen g) => Int -> Rand.Rand g a




newtype Note = N Int
    deriving (Show)
instance GenRandom Note where
    genRandom _ = N <$> Rand.uniform [0..7]

newtype Vel = V Double
    deriving (Show)
instance GenRandom Vel where
    genRandom _ = V <$> Rand.getRandomR (0,1)

data Beat 
    = Rest
    | Note Note Vel
    | Concat [Beat]
    deriving (Show)
instance GenRandom Beat where
    genRandom 0 = join $ Rand.uniform [pure Rest, Note <$> genRandom 0 <*> genRandom 0]
    genRandom d = join $ Rand.uniform [
        do s <- Rand.getRandomR (2,4)
           Concat <$> replicateM s (genRandom (d-1))
      ]


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
        interp conn beat
    return $ writeIORef ref
