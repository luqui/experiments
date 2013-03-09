{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, TypeOperators, GADTs #-}

module FGAlgebra where

import Control.Arrow ((***))

data (f :*: g) a = Pair (f a) (g a)
    deriving (Functor)

data (f :+: g) a
    = InL (f a)
    | InR (g a)
    deriving (Functor)

feither :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
feither f _ (InL fa) = f fa
feither _ g (InR ga) = g ga

pair :: (a -> b) -> (a -> c) -> a -> (b,c)
pair f g x = (f x, g x)

type Algebra f a = f a -> a
type Coalgebra g a = a -> g a

type FG f g a = (Algebra f a, Coalgebra g a)

commPair :: (Functor f) => f (a,b) -> (f a, f b)
commPair = pair (fmap fst) (fmap snd)

algProduct :: (Functor f) => Algebra f a -> Algebra f b -> Algebra f (a,b)
algProduct alga algb = (alga *** algb) . commPair

algCoproduct :: (Functor f, Functor g) 
          => Algebra f a -> Algebra g a -> Algebra (f :+: g) a
algCoproduct = feither


coalgProduct :: (Functor f) => Coalgebra f a -> Coalgebra g a -> Coalgebra (f :*: g) a
coalgProduct fcoalg gcoalg a = Pair (fcoalg a) (gcoalg a)

coalgCoproduct :: (Functor f) => Coalgebra f a -> Coalgebra f b -> Coalgebra f (Either a b)
coalgCoproduct coalga coalgb (Left a) = fmap Left (coalga a)
coalgCoproduct coalga coalgb (Right b) = fmap Right (coalgb b)


newtype NatTrans f g = NatTrans { getNatTrans :: forall a. f a -> g a }
data NatIso f g = NatIso (NatTrans f g) (NatTrans g f)

newtype Const b a = Const b
    deriving (Functor)

type Cone v d = NatTrans (Const v) d

newtype Cones d v = Cones (Cone v d)
newtype Arrows u v = Arrows (v -> u)

type Limit d u = NatIso (Cones d) (Arrows u)
newtype Algebra' f a  = Algebra' (Algebra f a)

algLimit :: (Functor f) => Limit d u -> NatTrans d (Algebra' f) -> Algebra f u
algLimit = undefined


data ProductD a b x where
    Fst :: ProductD a b a
    Snd :: ProductD a b b


data ZCon a 
    = ZZero
    | ZOne
    | ZAdd a a
    | ZSub a a
    deriving (Functor)

data ZObs a = ZObs {
    zSign   :: Ordering,
    zPred   :: a
}
    deriving (Functor)

class Z a where
    z_fg :: FG ZCon ZObs a

instance Z Integer where
    z_fg = (alg, coalg)
        where
        alg ZZero      = 0
        alg ZOne       = 1
        alg (ZAdd x y) = x + y
        alg (ZSub x y) = x - y

        coalg x = ZObs { 
            zSign = x `compare` 0, 
            zPred = x-1 
        }
