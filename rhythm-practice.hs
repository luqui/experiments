{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}

import Control.Monad (ap)
import Control.Monad.Random 
import Control.Concurrent (threadDelay)
import System.Console.ANSI (clearScreen, setCursorPosition)

newtype Gray a = Gray { getGray :: [a] }
    deriving (Eq, Ord, Show, Functor)

instance Monad Gray where
    return x = Gray [x]
    m >>= f = Gray . grayConcat $ map (getGray . f) (getGray m)

instance Applicative Gray where
    pure = return
    (<*>) = ap

grayConcat :: [[a]] -> [a]
grayConcat = concat . zipWith ($) (cycle [id,reverse])


class (Monad m) => MonadPick m where
    pick :: [a] -> m a

instance MonadPick [] where
    pick = id

instance MonadPick Gray where
    pick = Gray

instance (Monad m, RandomGen g) => MonadPick (RandT g m) where
    pick = fromList . map (, 1)


block :: (MonadPick m) => Int -> m [Bool]
block n = replicateM n (pick [False,True])

bar :: (MonadPick m) => [Int] -> m [[Bool]]
bar = mapM block

renderBar :: [[Bool]] -> String
renderBar = unwords . (map.map) renderBeat
    where
    renderBeat True = 'x'
    renderBeat False = '.'

game :: IO () -> [String] -> IO ()
game btw = mapM_ (\b -> showboard b >> btw)
    where
    showboard board = do
        clearScreen
        setCursorPosition 0 0
        putStrLn board

ignore :: IO a -> IO ()
ignore m = m >> return ()

repeatM :: (Monad m) => m a -> m [a]
repeatM m = do
    x <- m
    (x:) <$> repeatM m

wait :: Double -> IO ()
wait s = threadDelay (floor (10^6 * s))

enter :: IO ()
enter = ignore getLine

randomGame :: [Int] -> IO () ->  IO () 
randomGame divs btw = game btw  =<< evalRandIO (repeatM (renderBar <$> bar divs))

grayGame :: [Int] -> IO () -> IO ()
grayGame divs btw = game btw . getGray $ renderBar <$> bar divs


