{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, TypeOperators, KindSignatures, ConstraintKinds, RankNTypes, MultiParamTypeClasses, UndecidableInstances, ScopedTypeVariables, FunctionalDependencies, FlexibleInstances, FlexibleContexts #-}

import Data.Constraint
import Data.Constraint.Forall
import Data.Proxy

data KindTree
    = Set
    | KindTree :->: KindTree

-- Eq1 for greater values of 1.
newtype Eq0 a = Eq0 { eq0 :: a -> a -> Bool }

newtype Eqk kt kt' f = Eqk { eqk :: forall a. Eqn kt a -> Eqn kt' (f a) }

type family Eqn (kt :: KindTree) :: k -> * where
    Eqn Set = Eq0
    Eqn (kt :->: kt') = Eqk kt kt'

eqBool :: Eqn 'Set Bool
eqBool = Eq0 (==)

eqMaybe :: Eqn ('Set :->: 'Set) Maybe
eqMaybe = Eqk (\eqa -> Eq0 (\m m' ->
    case (m, m') of
        (Just x, Just y) -> eq0 eqa x y
        (Nothing, Nothing) -> True
        _ -> False))


-- Here it is with classes.  Pretty neat, though the Eq (Mu f) instance is pretty messy
-- with all the type hints, and also brittle as to which type hints work and which don't.
class (EqnC kt a :=> EqnC kt' (f a)) => EqkCHelper kt kt' f a
instance (EqnC kt a :=> EqnC kt' (f a)) => EqkCHelper kt kt' f a

class (Forall (EqkCHelper kt kt' f)) => EqkC kt kt' f
instance (Forall (EqkCHelper kt kt' f)) => EqkC kt kt' f

type family EqnC (kt :: KindTree) :: k -> Constraint where
    EqnC Set = Eq
    EqnC (kt :->: kt') = EqkC kt kt'


newtype Mu f = Roll { unroll :: f (Mu f) }

instance EqnC (Set :->: Set) f => Eq (Mu f) where
    Roll x == Roll y
        -- I'd like to say inst :: EqnC (Set :->: Set) f :- ..., but GHC rejects this.
        | Sub Dict <- (inst :: Forall (EqkCHelper Set Set f) :- EqkCHelper Set Set f (Mu f)) 
        , Sub Dict <- (ins :: Eq (Mu f) :- Eq (f (Mu f)))
            = x == y


