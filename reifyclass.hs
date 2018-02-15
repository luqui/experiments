{-# LANGUAGE PolyKinds, ConstraintKinds, TypeFamilies, ConstrainedClassMethods, RankNTypes, ScopedTypeVariables, FlexibleContexts, UndecidableInstances, TypeApplications #-}

import qualified Data.Constraint as Contraint
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy
import Data.Reflection

data Iso a b = Iso { to :: a -> b, from :: b -> a }

class HasDict c where
    data Dict c :: * -> *
    getDict :: c a => Dict c a
    putDict :: Dict c a -> (forall b. c b => Iso a b -> r) -> r

newtype FCEq p a = FCEq { getFCEq :: a }

instance Reifies p (Dict Eq a) => Eq (FCEq p a) where
    FCEq a == FCEq b = let EqDict eq _ = reflect (Proxy :: Proxy p) in eq a b
    FCEq a /= FCEq b = let EqDict _ ne = reflect (Proxy :: Proxy p) in ne a b

instance HasDict Eq where
    data Dict Eq a = EqDict (a -> a -> Bool) (a -> a -> Bool)
    getDict = EqDict (==) (/=)
    putDict dict f = reify dict (\(_ :: Proxy p) -> f @(FCEq p _) (Iso FCEq getFCEq))

example :: Bool
example = putDict (EqDict eq ((result.result) not eq)) $ \iso -> to iso 4 == to iso 6
    where
    eq x y = x `mod` 2 == y `mod` 2
    result = (.)
