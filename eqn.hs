{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, TypeOperators, KindSignatures, ConstraintKinds, RankNTypes, MultiParamTypeClasses, UndecidableInstances, ScopedTypeVariables, FunctionalDependencies, FlexibleInstances #-}

import Data.Constraint
import Data.Proxy

data KindTree
    = Set
    | KindTree :->: KindTree

-- Eq1 for greater values of 1.
-- TODO, implement it as a class using Data.Constraint.
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




class EqkC kt kt' f | f -> kt kt'  where
    eqkC :: Proxy f -> Proxy a -> EqnC kt a :- EqnC kt' (f a)

type family EqnC (kt :: KindTree) :: k -> Constraint where
    EqnC Set = Eq
    EqnC (kt :->: kt') = EqkC kt kt'

instance EqkC Set Set Maybe where eqkC _ _ = Sub Dict


newtype Mu f = Roll { unroll :: f (Mu f) }

instance EqnC (Set :->: Set) f => Eq (Mu f) where
    Roll x == Roll y
        | Sub Dict <- eqkC (Proxy :: Proxy f) (Proxy :: Proxy (Mu f)) = x == y

instance EqkC (Set :->: Set) Set Mu where eqkC _ _ = Sub Dict
