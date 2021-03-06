{-# LANGUAGE ConstraintKinds, RankNTypes, TypeFamilies, AllowAmbiguousTypes, DataKinds, PolyKinds, TypeOperators, MultiParamTypeClasses, UndecidableInstances, FlexibleInstances #-}

import Data.Constraint (Constraint)
import qualified Text.ParserCombinators.ReadP as ReadP
import Text.ParserCombinators.ReadP (ReadP)

type family All f xs :: Constraint where
    All f '[] = ()
    All f (x ': xs) = (f x, All f xs)

data Proxy a = Proxy

class All c (InnerTypes a) => GParse c a where
    type InnerTypes a :: [*]
    gparse :: (Applicative f) => Proxy c -> (forall x. c x => f x) -> f a

data Foo = Foo Bool Int String 
    deriving Show

instance All c (InnerTypes Foo) => GParse c Foo where
    type InnerTypes Foo = '[Bool, Int, String]
    gparse _ r = Foo <$> r <*> r <*> r

readFoo :: ReadP.ReadP Foo
readFoo = gparse (Proxy :: Proxy Read) (ReadP.readS_to_P reads)
