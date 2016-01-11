import Control.Applicative
import Control.Concurrent (threadDelay)
import Control.Monad (replicateM_)
import qualified System.MIDI as MIDI

note :: Int -> Int
note 0 = 60
note 1 = 62
note 2 = 64
note 3 = 65
note 4 = 67
note 5 = 69
note 6 = 71
note 7 = 72

playNote :: MIDI.Connection -> Int -> Double -> IO ()
playNote conn n v = do
    MIDI.send conn (MIDI.MidiMessage 1 (MIDI.NoteOn (note n) (floor (127 * v))))
    MIDI.send conn (MIDI.MidiMessage 1 (MIDI.NoteOn (note n) 0))

delay :: Double -> IO ()
delay sec = threadDelay (floor (10^6 * sec))

main :: IO ()
main = do
    conn <- MIDI.openDestination =<< head <$> MIDI.enumerateDestinations
    replicateM_ 8 $ do
        playNote conn 0 1
        delay (1/2)
        playNote conn 1 1
        delay (1/2)
    MIDI.close conn
