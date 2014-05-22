{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, TypeOperators, TupleSections, FlexibleContexts #-}

import Control.Applicative
import Data.Monoid (Monoid(..), (<>))
import Control.Monad (ap)
import Data.Function (on)
import Data.List (insertBy)
import Data.Ord (Down(..))
import Data.Maybe (catMaybes)
import Data.Foldable
import Data.Traversable

-- An FRP based on the situation calculus.

newtype Time = Time Integer
    deriving (Eq, Ord)


data Event a = Event { eTime :: Time, eValue :: a }
    deriving (Functor, Foldable, Traversable)

newtype History a = History { getHistory :: [Event a] }

mergeOn :: (Ord b) => (a -> b) -> [a] -> [a] -> [a]
mergeOn f [] ys = ys
mergeOn f xs [] = xs
mergeOn f (x:xs) (y:ys) =
    case compare (f x) (f y) of
        LT -> x:mergeOn f xs (y:ys)
        EQ -> x:y:mergeOn f xs ys
        GT -> y:mergeOn f (x:xs) ys
    where
    fx = f x
    fy = f y

instance Monoid (History a) where
    mempty = History []
    History xs `mappend` History ys = History (mergeOn (Down . eTime) xs ys)

newtype Fluent e a = Fluent { runFluent :: History e -> a }
    deriving (Functor)

instance Monad (Fluent e) where
    return = Fluent . const
    m >>= f = Fluent $ \es -> runFluent (f (runFluent m es)) es

instance Applicative (Fluent e) where
    pure = return
    (<*>) = ap


type (+) = Either
type (*) = (,)

narrowHistory :: (e -> Maybe e') -> History e -> History e'
narrowHistory f = History . catMaybes . map (sequenceA . fmap f) . getHistory

narrow :: (e -> Maybe e') -> Fluent e' a -> Fluent e a
narrow f = Fluent . (argument.narrowHistory) f . runFluent
    where
    argument = flip (.)


-- f is intended to be some sort of "set" w/ union. 
newtype Situation f e a = Situation { getSituation :: Fluent e (f e, a) }
    deriving (Functor)

instance (Monoid (f e)) => Applicative (Situation f e) where
    pure = return
    (<*>) = ap

instance (Monoid (f e)) => Monad (Situation f e) where
    return = Situation . return . (mempty,)
    m >>= f = Situation $ do
        (e,x) <- getSituation m
        (e',y) <- getSituation (f x)
        return (e <> e', y)


