{-# LANGUAGE GeneralizedNewtypeDeriving, LambdaCase #-}

import Control.Concurrent
import Control.Concurrent.MVar
import Control.Exception (mask_)
import Control.Monad.IO.Class
import qualified Control.Monad.Trans.Reader as Reader
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad (unless, forever)
import Control.Applicative
import Data.Monoid

data UnambTree
    = Vanished
    | Leaf ThreadId
    | Branch ThreadId (MVar UnambTree) (MVar UnambTree)

newtype Engine a = Engine { runEngine :: ReaderT (MVar UnambTree) IO a }
    deriving (Functor, Applicative, Monad, MonadIO)

localRoot :: MVar UnambTree -> Engine a -> Engine a
localRoot root e = Engine . ReaderT $ \_ -> runReaderT (runEngine e) root

ask :: Engine (MVar UnambTree)
ask = Engine Reader.ask

killTree :: MVar UnambTree -> IO ()
killTree mv = mask_ $ do
    takeMVar mv >>= \case
        Vanished -> return ()
        Leaf tid -> killThread tid 
        Branch tid lv rv -> do
            killTree lv
            killTree rv
            killThread tid
    putMVar mv Vanished

runThread :: MVar UnambTree -> MVar UnambTree -> MVar a -> Engine a -> IO ()
runThread self other result body = do
    putMVar self . Leaf =<< myThreadId
    putMVar result =<< runReaderT (runEngine body) self
    killTree other
    

unamb :: Engine a -> Engine a -> Engine a
unamb a b = do
    (amv,bmv,result) <- liftIO $ (,,) <$> newEmptyMVar <*> newEmptyMVar <*> newEmptyMVar
    root <- ask
    liftIO $ do
        tid <- myThreadId
        _ <- swapMVar root (Branch tid amv bmv)
        forkIO $ runThread amv bmv result a
        forkIO $ runThread bmv amv result b
        r <- takeMVar result 
        _ <- swapMVar root (Leaf tid)
        return r

thunk :: Engine a -> Engine (Engine a)
thunk c = do
    var <- liftIO $ newMVar Nothing
    return $ do
        r <- maybe c return =<< liftIO (takeMVar var)
        liftIO $ putMVar var (Just r)
        return r

bottom :: Engine a
bottom = do
    root <- ask
    liftIO $ do
        Leaf tid <- swapMVar root Vanished
        killThread tid
    undefined

infiniteLoop :: Engine a
infiniteLoop = forever tick

tick :: Engine ()
tick = liftIO yield

instance Semigroup (Engine a) where
    (<>) = unamb
    
instance Monoid (Engine a) where
    mempty = bottom

pfold :: (Monoid m) => [m] -> m 
pfold [] = mempty
pfold [x] = x
pfold xs = pfold (pairUp xs)
    where
    pairUp [] = []
    pairUp [x] = [x]
    pairUp (x:y:xs) = (x <> y) : pairUp xs

mainE :: Engine Int
mainE = do
    r <- pfold $ map test [0..100000]
    return r
    where
    test 99999 = return 99999
    test _ = infiniteLoop



main = do
    root <- newMVar . Leaf =<< myThreadId
    print =<< runReaderT (runEngine mainE) root
