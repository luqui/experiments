import Control.Applicative
import Control.Concurrent (threadDelay, forkIO)
import Control.Monad (replicateM, replicateM_, forever, join)
import Data.IORef
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

interp :: MIDI.Connection -> Double -> Beat -> IO ()
interp conn tempo = go (4*60/tempo)
    where
    go time Rest = delay time
    go time (Note n v) = playNote conn n v >> delay time
    go time (Concat bs) = mapM_ (go (time / fromIntegral (length bs))) bs

mkPlayer :: IO (Beat -> IO ())
mkPlayer = do
    conn <- MIDI.openDestination =<< head <$> MIDI.enumerateDestinations
    ref <- newIORef Rest
    _ <- forkIO . forever $ do
        beat <- readIORef ref
        interp conn 100 beat
    return $ writeIORef ref
