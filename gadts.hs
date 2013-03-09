{-# LANGUAGE GeneralizedNewtypeDeriving, GADTs #-}

import Prelude hiding (Eq)

data Eq a b where
    Refl :: Eq a a

coerce :: Eq a b -> a -> b
coerce Refl = id

trans :: Eq a b -> Eq b c -> Eq a c
trans Refl Refl = Refl

sameUnit :: Eq () ()
sameUnit = Refl

class IsoUnit a where
    iso1 :: Eq () b -> Eq a b
    iso2 :: Eq b () -> Eq b a

instance IsoUnit () where
    iso1 = id
    iso2 = id

newtype Tagged a b = Tagged b deriving IsoUnit

sameTagged :: Eq (Tagged a b) (Tagged a' b') -> Eq a a'
sameTagged Refl = Refl

unsafe' :: Eq (Tagged a ()) (Tagged a' ())
unsafe' = iso1 sameUnit `trans` iso2 sameUnit

unsafe :: Eq a b
unsafe = sameTagged unsafe'

unsafeCoerce = coerce unsafe
