{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, TypeOperators, KindSignatures, ConstraintKinds, RankNTypes, MultiParamTypeClasses, UndecidableInstances, ScopedTypeVariables, FunctionalDependencies, FlexibleInstances, FlexibleContexts, AllowAmbiguousTypes #-}

-- This experiment generalizes Eq1 to greater values of 1. This works in theory, but fails
-- due to missing :=>: instances that are illegal because of Forall.  This can be made to work,
-- but with more boilerplate than I was hoping for.

import Data.Constraint
import Data.Constraint.Forall
import Data.Proxy

data KindTree
    = Set
    | KindTree :->: KindTree


-- notational convenience
data Proxy4 a b c d = Proxy4

-- Here it is with classes. It's pretty cool that the complexity is at the use
-- site, and we don't need any boilerplate to specify that something is Eqn
-- beyond the actual instance existing.
class (EqnC kt a :=> EqnC kt' (f a)) => EqkCHelper kt kt' f a
instance (EqnC kt a :=> EqnC kt' (f a)) => EqkCHelper kt kt' f a

class (Forall (EqkCHelper kt kt' f)) => EqkC kt kt' f
instance (Forall (EqkCHelper kt kt' f)) => EqkC kt kt' f

type family EqnC (kt :: KindTree) :: k -> Constraint where
    EqnC Set = Eq
    EqnC (kt :->: kt') = EqkC kt kt'

useEqnC :: forall k k' f a. (EqnC (k :->: k') f, EqnC k a) 
        => Proxy4 k k' f a -> Dict (EqnC k' (f a))
useEqnC _
    | Sub Dict <- (inst :: Forall (EqkCHelper k k' f) :- EqkCHelper k k' f a)
    , Sub Dict <- (ins :: EqnC k a :- EqnC k' (f a))
    = Dict

newtype Mu f = Roll { unroll :: f (Mu f) }

instance EqnC (Set :->: Set) f => Eq (Mu f) where
    Roll x == Roll y
        | Dict <- useEqnC (Proxy4 :: Proxy4 Set Set f (Mu f))
        = x == y

itWorks = Roll (Just (Roll (Just (Roll Nothing)))) == Roll (Just (Roll Nothing))



newtype Mu1 f a = Roll1 { unroll1 :: f (Mu1 f a) a }

instance (EqnC (Set :->: (Set :->: Set)) f, EqnC Set a) => Eq (Mu1 f a) where
    Roll1 x == Roll1 y
        | Dict <- useEqnC (Proxy4 :: Proxy4 Set (Set :->: Set) f (Mu1 f a))
        , Dict <- useEqnC (Proxy4 :: Proxy4 Set Set (f (Mu1 f a)) a)
        = x == y

data Maybe2 a b = Nothing2 | Just2 a b
    deriving (Eq)

-- Maybe I was a bit optimistic. This doesn't work.
--itWorks' = Roll1 (Just2 (Roll1 Nothing2) True) == Roll1 (Just2 (Roll1 Nothing2) True)
