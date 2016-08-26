{-# LANGUAGE ConstraintKinds, DeriveFunctor, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction, TypeFamilies, PolyKinds, RankNTypes, TypeOperators, GADTs, LambdaCase #-}

import qualified Prelude
import Prelude hiding (Num(..), Monoid(..), Functor(..))

class Endofunctor f where
    type Cat f :: k -> k -> *
    fmap :: Cat f a b -> Cat f (f a) (f b)

class (Endofunctor f) => Reg f a where
    reg :: Cat f (f a) a

instance (Reg f a, Reg f b, Cat f ~ (->)) => Reg f (a,b) where
    reg f = (reg (fmap fst f), reg (fmap snd f))


reg0 :: (Reg f a, Cat f ~ (->)) => f a -> a
reg0 f = reg f

reg1 :: (Reg f b, Cat f ~ (->)) => (a -> f b) -> a -> b
reg1 f x = reg (f x)

reg2 :: (Reg f c, Cat f ~ (->)) => (a -> b -> f c) -> a -> b -> c
reg2 f x y = reg (f x y)

data NumF a
    = FromInteger Integer
    | Plus a a
    | Minus a a
    | Negate a
    | Times a a
    | Abs a
    | SigNum a
    deriving (Prelude.Functor)

instance Endofunctor NumF where
    type Cat NumF = (->)
    fmap = Prelude.fmap

type Num = Reg NumF

fromInteger = reg1 FromInteger
(+) = reg2 Plus
(-) = reg2 Minus
negate = reg1 Negate
(*) = reg2 Times
abs = reg1 Abs
signum = reg1 SigNum

instance Reg NumF Integer where
    reg (FromInteger n) = Prelude.fromInteger n
    reg (Plus a b) = a Prelude.+ b
    reg (Minus a b) = a Prelude.- b
    reg (Negate a) = Prelude.negate a
    reg (Times a b) = a Prelude.* b
    reg (Abs a) = Prelude.abs a
    reg (SigNum a) = Prelude.signum a


data MonoidF a
    = MEmpty
    | MAppend a a
    deriving (Prelude.Functor)

instance Endofunctor MonoidF where
    type Cat MonoidF = (->)
    fmap = Prelude.fmap

type Monoid = Reg MonoidF

mempty = reg0 MEmpty
mappend = reg2 MAppend

instance Reg MonoidF [a] where
    reg MEmpty = []
    reg (MAppend x y) = x ++ y

-- Now let's get high

newtype f ~> g = Nat { appNat :: forall x. f x -> g x }

data FunctorF :: (* -> *) -> (* -> *) where
    FMap :: (a -> b) -> f a -> FunctorF f b

instance Endofunctor FunctorF where
    type Cat FunctorF = (~>)
    fmap f = Nat $ \(FMap t a) -> FMap t (appNat f a)

type Functor = Reg FunctorF

fmap' :: (Functor f) => (a -> b) -> (f a -> f b)
fmap' f x = appNat reg (FMap f x)

instance Reg FunctorF Maybe where
    reg = Nat $ \case
        FMap f Nothing -> Nothing
        FMap f (Just x) -> Just (f x)
