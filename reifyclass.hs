{-# LANGUAGE PolyKinds, ConstraintKinds, TypeFamilies, ConstrainedClassMethods, RankNTypes, ScopedTypeVariables, FlexibleContexts, UndecidableInstances, TypeApplications, TypeOperators #-}

-- Here is a way to create "local data types" with an associated instance (of a unary class).

import qualified Data.Constraint as Contraint
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy
import Data.Reflection


data family (~>) :: k -> k -> *
data instance a ~> b = NT0 { apply0 :: a -> b }
data instance a ~> b = NTS { applyS :: forall s. a s ~> b s }

data Eqv a b = Eqv { to :: a ~> b, from :: b ~> a }

class HasDict c where
    data Dict c :: k -> *
    getDict :: c a => Dict c a
    putDict :: Dict c a -> (forall b. c b => Eqv a b -> r) -> r

-- For each class you want to do with this, you make this boilerplate )-:

newtype FCEq p a = FCEq { getFCEq :: a }

instance Reifies p (Dict Eq a) => Eq (FCEq p a) where
    FCEq a == FCEq b = let EqDict eq _ = reflect (Proxy :: Proxy p) in eq a b
    FCEq a /= FCEq b = let EqDict _ ne = reflect (Proxy :: Proxy p) in ne a b

instance HasDict Eq where
    data Dict Eq a = EqDict (a -> a -> Bool) (a -> a -> Bool)
    getDict = EqDict (==) (/=)
    putDict dict r = reify dict (\(_ :: Proxy p) -> r @(FCEq p _) (Eqv (NT0 FCEq) (NT0 getFCEq)))

-- Then you use it like this:
exampleEq :: Bool
exampleEq = putDict (EqDict eq ((result.result) not eq)) $ \iso -> apply0 (to iso) 4 == apply0 (to iso) 6
    where
    eq x y = x `mod` 2 == y `mod` 2
    result = (.)


-- It works at higher kinds too:
newtype FCFunctor p f a = FCFunctor { getFCFunctor :: f a }

instance Reifies p (Dict Functor f) => Functor (FCFunctor p f) where
    fmap f (FCFunctor x) = let FunctorDict fmap' = reflect (Proxy :: Proxy p) in FCFunctor (fmap' f x)

instance HasDict Functor where
    data Dict Functor f = FunctorDict (forall a b. (a -> b) -> f a -> f b)
    getDict = FunctorDict fmap
    putDict dict r = reify dict (\(_ :: Proxy p) -> r @(FCFunctor p _) (Eqv (NTS (NT0 FCFunctor)) (NTS (NT0 getFCFunctor))))

exampleFunctor :: Maybe Int
exampleFunctor = putDict (FunctorDict (\_ _ -> Nothing)) $ \iso -> apply0 (applyS (from iso)) (fmap succ (apply0 (applyS (to iso)) (Just 42)))
