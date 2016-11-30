{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, TypeOperators, KindSignatures, ConstraintKinds, RankNTypes #-}

import Data.Constraint

data KindTree
    = Set
    | KindTree :->: KindTree

-- Cool thing, reify a KindTree into a lifted kind (k -> *) -> *.
newtype Id a = Id a

newtype KArr k k' a = KArr (k a -> k' a)

type family Reify (kt :: KindTree) :: k -> * where
    Reify Set = Id
    Reify (k :->: k') = KArr (Reify k) (Reify k')


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
