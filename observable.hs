{-# LANGUAGE TypeOperators, ConstraintKinds, GADTs, RankNTypes, ScopedTypeVariables, GeneralizedNewtypeDeriving, DeriveFunctor, DefaultSignatures, TypeFamilies, EmptyDataDecls, LambdaCase #-}

import Data.Void (Void, absurd)
import Data.Kind (Constraint)

data Ex f where
    Ex :: f a -> Ex f

newtype (c := f) a = Cx (c a => f a)

type ExC c f = Ex (c := f)

newtype Mu f = Mu { getMu :: f (Mu f) }
newtype (f · g) a = Comp { getComp :: f (g a) }
    deriving (Functor)

newtype Obs g a = Obs { getObs :: forall b. g b a -> b }

data ClassRep f g a = ClassRep (f a -> a) (Obs g a)

newtype ExClass f g = ExClass (Obs g (Mu f))

class Functor2 g where
    fmap2 :: (a -> b) -> g c a -> g c b
    default fmap2 :: (Functor (g c)) => (a -> b) -> g c a -> g c b
    fmap2 = fmap

reify :: (Functor f, Functor2 g) => Ex (ClassRep f g) -> ExClass f g
reify (Ex (ClassRep alg obs)) = ExClass (Obs (getObs obs . fmap2 rec))
    where
    rec (Mu fmu) = alg (fmap rec fmu)
        
exify :: ExClass f g -> Ex (ClassRep f g)
exify (ExClass f) = Ex (ClassRep Mu f)



class Repr (c :: * -> Constraint) where
    data AlgF c :: * -> *
    data ObsF c :: * -> * -> *
    algRepr :: c a => AlgF c a -> a
    obsRepr :: c a => ObsF c b a -> b
    repr :: c a => ClassRep (AlgF c) (ObsF c) a
    repr = ClassRep algRepr (Obs obsRepr)

instance Repr Eq where
    data AlgF Eq a where
    data ObsF Eq b a where
        MEquals :: a -> a -> ObsF Eq Bool a
    algRepr = error "impossible"
    obsRepr (MEquals x y) = x == y


newtype (f +++ f') a = Coprod (Either (f a) (f' a))

newtype (f ++++ f') b a = Coprod1 (Either (f b a) (f' b a))

join :: ClassRep f g a -> ClassRep f' g' a -> ClassRep (f +++ f') (g ++++ g') a
join (ClassRep alg obs) (ClassRep alg' obs') = ClassRep
    (\case { Coprod (Left x) -> alg x ; Coprod (Right x) -> alg' x })
    (Obs (\case { Coprod1 (Left x) -> getObs obs x ; Coprod1 (Right x) -> getObs obs' x }))


data PairObs g g' b a where
    PairObs :: g b a -> g' b' a' -> PairObs g g' (b,b') (a,a')

tuple :: (Functor f) => ClassRep f g a -> ClassRep f g b -> ClassRep f (PairObs g g) (a,b)
tuple (ClassRep alg obs) (ClassRep alg' obs') = 
    ClassRep (\x -> (alg (fmap fst x), alg' (fmap snd x)))
             (Obs (\(PairObs g g') -> (getObs obs g, getObs obs' g')))
