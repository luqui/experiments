{-# LANGUAGE ConstraintKinds, DeriveFunctor, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NoMonomorphismRestriction #-}

import qualified Prelude
import Prelude hiding (Num(..), Monoid(..))

type Algebra f a = f a -> a

class (Functor f) => Reg f a where
    reg :: Algebra f a

instance (Reg f a, Reg f b) => Reg f (a,b) where
    reg f = (reg (fmap fst f), reg (fmap snd f))


reg0 :: (Reg f a) => f a -> a
reg0 f = reg f

reg1 :: (Reg f b) => (a -> f b) -> a -> b
reg1 f x = reg (f x)

reg2 :: (Reg f c) => (a -> b -> f c) -> a -> b -> c
reg2 f x y = reg (f x y)

data NumF a
    = FromInteger Integer
    | Plus a a
    | Minus a a
    | Negate a
    | Times a a
    | Abs a
    | SigNum a
    deriving (Functor)

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
    deriving (Functor)

type Monoid = Reg MonoidF

mempty = reg0 MEmpty
mappend = reg2 MAppend

instance Reg MonoidF [a] where
    reg MEmpty = []
    reg (MAppend x y) = x ++ y

