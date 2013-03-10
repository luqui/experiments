{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, DeriveFunctor, DeriveFoldable, DoRec, ViewPatterns #-}

import Prelude hiding (mapM_, cycle)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import System.IO.Unsafe (unsafePerformIO)
import Control.Applicative
import Data.Supply (Supply, split2, newSupply, supplyValue)
import Control.Monad (ap, join)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Trans.State (execState, get, put)
import Data.Foldable (Foldable, foldMap)
import Data.Monoid ((<>))


newtype SupplyM v a = SupplyM { getSupplyM :: Supply v -> a }

supply :: SupplyM v v
supply = SupplyM supplyValue

instance Functor (SupplyM v) where
    fmap f (SupplyM s) = SupplyM (f . s)

instance Applicative (SupplyM v) where
    pure = return
    (<*>) = ap

instance Monad (SupplyM v) where
    return = SupplyM . const
    SupplyM m >>= f = SupplyM $ \s -> 
        let (s',s'') = split2 s in
        getSupplyM (f (m s')) s''

instance MonadFix (SupplyM v) where
    mfix f = SupplyM (\s -> let x = getSupplyM (f x) s in x)


newtype Label s = Label Integer
    deriving (Eq, Ord)

newtype RecM s a = RecM { getRecM :: SupplyM (Label s) a }
    deriving (Functor, Applicative, Monad, MonadFix)

newLabel :: RecM s (Label s)
newLabel = RecM supply

{-# NOINLINE runRecM #-}
runRecM :: (forall s. RecM s a) -> a
runRecM (RecM m) = getSupplyM m (unsafePerformIO (newSupply (Label 0) (\(Label x) -> Label (x+1))))



data Rec s f = Rec (Label s) (f (Rec s f))

label :: Rec s f -> Label s
label (Rec l _) = l

roll :: f (Rec s f) -> RecM s (Rec s f)
roll frec = do
    l <- newLabel
    return (Rec l frec)

unroll :: Rec s f -> f (Rec s f)
unroll (Rec _ frec) = frec


class (Eq a) => Lattice a where
    (\/) :: a -> a -> a
    bottom :: a


backwardFix :: (Lattice a, Functor f, Foldable f) => (f a -> a) -> Rec s f -> a
backwardFix f = \m -> getInfo (execState (go (Seq.singleton m)) Map.empty) m
    where
    go (Seq.viewl -> Seq.EmptyL) = return ()
    go (Seq.viewl -> Rec l fr Seq.:< seq)  = do
        mp <- get
        let info  = maybe bottom id (Map.lookup l mp)
            infos = fmap (getInfo mp) fr
            info' = f infos
        if info' /= info
            then do
                put (Map.insert l info' mp)
                go (seq <> foldMap Seq.singleton fr <> Seq.singleton (Rec l fr))
            else
                go seq

    getInfo mp r = maybe bottom id (Map.lookup (label r) mp)



data RCell a r = Nil | Cons a r
    deriving (Functor, Foldable)

type RList s a = Rec s (RCell a)

cons :: a -> RList s a -> RecM s (RList s a)
cons x xs = roll (Cons x xs)

append :: RList s a -> RList s a -> RecM s (RList s a)
append rl rl' = 
    case unroll rl of
        Nil -> return rl'
        Cons x xs -> cons x =<< append xs rl'

fromList :: [a] -> RecM s (RList s a)
fromList [] = roll Nil
fromList (x:xs) = cons x =<< fromList xs

toList :: RList s a -> [a]
toList r = 
    case unroll r of
        Nil -> []
        Cons x xs -> x : toList xs

cycle :: RList s a -> RecM s (RList s a)
cycle xs = do
    rec r <- append xs r
    return r


instance (Ord a) => Lattice (Set.Set a) where
    (\/) = Set.union
    bottom = Set.empty

elements :: (Ord a) => RList s a -> Set.Set a
elements = backwardFix go
    where
    go Nil = Set.empty
    go (Cons a r) = Set.insert a r
