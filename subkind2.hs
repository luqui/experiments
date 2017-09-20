{-# LANGUAGE TypeInType, GADTs, RankNTypes, ConstraintKinds, DataKinds, PolyKinds, AllowAmbiguousTypes, TypeFamilies #-}

import Data.Kind (Type, Constraint)

-- Pi, Sigma :: (A :: Type) -> (F :: A -> Type) -> Type

data family Sing a :: a -> Type

data instance Sing Bool b where
    STrue :: Sing Bool True
    SFalse :: Sing Bool False

newtype Pi (a :: Type) (f :: a -> Type) = MkPi { getPi :: forall (x :: a). Sing a x -> f x }

type family Cond a b x where
    Cond a b True = a
    Cond a b False = b

newtype CondT a b x = CondT { getCondT :: Cond a b x }

type Prod a b = Pi Bool (CondT a b)

boolInd :: f True -> f False -> forall (x :: Bool). Sing Bool x -> f x
boolInd t f STrue = t
boolInd t f SFalse = f

iso1 :: (a,b) -> Prod a b
iso1 (x,y) = MkPi (boolInd (CondT x) (CondT y))

iso2 :: Prod a b -> (a,b)
iso2 pi = (getCondT (getPi pi STrue), getCondT (getPi pi SFalse))

{-
newtype SigmaC f r a = MkSigmaC (f a -> r)
newtype Sigma (a :: Type) (f :: a -> Type) = 
    MkSigma (forall r. Pi a (SigmaC f r) -> r)

type family Proj1 (x :: Sigma a f) where
    Proj1 (MkSigma f) = Any

data Dict c a where
    MkDict :: c a => Dict c a

less :: forall (k :: Sigma Type (Dict Ord)). Bool  -> Bool
less = undefined
-}
