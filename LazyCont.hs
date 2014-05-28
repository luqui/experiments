
import Data.Lub
import Data.Glb
import Control.Monad (liftM)

newtype LazyCont r a = LC { getLC :: (a -> r) -> r }

runLC :: (HasLub r) => LazyCont r a -> (a -> r) -> r
runLC lc c = c undefined `lub` getLC lc c

instance (HasLub r) => Functor (LazyCont r) where
    fmap = liftM

instance (HasLub r) => Monad (LazyCont r) where
    return x = LC $ \c -> c x
    m >>= f = LC $ \c -> runLC m (\x -> runLC (f x) c)


test :: (HasLub r) => LazyCont r [Int]
test = fmap (0:) test

main = print $ runLC test id
-- performance is off the charts!
