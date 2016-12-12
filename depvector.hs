{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeInType, GADTs, TypeOperators, RankNTypes, TypeFamilies, UndecidableInstances, TypeApplications, ScopedTypeVariables, AllowAmbiguousTypes, NoMonomorphismRestriction #-}

import Data.Kind (Type)
import Data.Foldable (toList)
import Debug.Trace

data Proxy a = Proxy

data (==) :: forall a. a -> a -> Type where
    Refl :: x == x

cong :: forall (k :: Type) (k' :: Type) (f :: k -> k') (a :: k) (b :: k). a == b -> f a == f b
cong Refl = Refl

eqSym :: a == b -> b == a
eqSym Refl = Refl

transport :: forall (k :: Type) (f :: k -> Type) (a :: k) (b :: k).  a == b -> f a -> f b
transport Refl = id

data Nat :: Type where
    Zero :: Nat
    Suc :: Nat -> Nat
    deriving (Show)

type family (+) a b :: Nat where
    'Zero + b = b
    'Suc a + b = 'Suc (a + b)

class NatProp (p :: Nat -> Type) where
    baseCaseN :: p 'Zero
    indCaseN  :: p n -> p ('Suc n)

data (p /\ q) x = Product (p x) (q x)
projL :: (p /\ q) x -> p x
projL (Product p _) = p
projR :: (p /\ q) x -> q x
projR (Product _ q) = q

instance (NatProp p, NatProp q) => NatProp (p /\ q) where
    baseCaseN = Product baseCaseN baseCaseN
    indCaseN (Product p q)  = Product (indCaseN p) (indCaseN q)

class IsNat (n :: Nat) where
    natRec :: p 'Zero -> (forall m. p m -> p ('Suc m)) -> p n
    natProp :: NatProp p => p n
    natProp = natRec baseCaseN indCaseN
instance IsNat 'Zero where natRec z _ = z
instance IsNat n => IsNat ('Suc n) where natRec z s = s (natRec z s)

newtype PlusZeroRight n = PlusZeroRight { getPlusZeroRight :: (n + 'Zero) == n }
instance NatProp PlusZeroRight where
    baseCaseN = PlusZeroRight Refl
    indCaseN (PlusZeroRight Refl) = PlusZeroRight Refl

newtype PlusSucRight n = PlusSucRight { getPlusSucRight :: forall m. Proxy m -> (n + 'Suc m) == 'Suc (n + m) }
instance NatProp PlusSucRight where
    baseCaseN = PlusSucRight (const Refl)
    indCaseN (PlusSucRight f) = trace "indCase" $ PlusSucRight (\proxy -> case f proxy of Refl -> Refl)

plusZeroRight :: IsNat n => (n + 'Zero) == n
plusZeroRight = getPlusZeroRight natProp

plusSucRight :: forall m n. IsNat n => (n + 'Suc m) == 'Suc (n + m) 
plusSucRight = getPlusSucRight @n natProp (Proxy :: Proxy m)


data Vector :: Nat -> Type -> Type where
    Nil :: forall a. Vector 'Zero a
    Cons :: forall n a. a -> Vector n a -> Vector ('Suc n) a

instance Foldable (Vector n) where
    foldMap _ Nil = mempty
    foldMap f (Cons x xs) = f x `mappend` foldMap f xs

instance (Show a) => Show (Vector n a) where
    show = show . toList

appendV :: Vector n a -> Vector m a -> Vector (n+m) a
appendV Nil ys = ys
appendV (Cons x xs) ys = Cons x (appendV xs ys)

zipV :: Vector n a -> Vector n b -> Vector n (a,b)
zipV Nil Nil = Nil
zipV (Cons x xs) (Cons y ys) = Cons (x,y) (zipV xs ys)

type RevProps = PlusZeroRight /\ PlusSucRight

reverseV :: Vector n a -> Vector n a
reverseV = go baseCaseN Nil
    where
    go :: forall m n a. RevProps n -> Vector n a -> Vector m a -> Vector (n+m) a
    go props accum Nil = transportVZ' (projL props) accum
    go props accum (Cons x xs) = goIndStep props accum (Cons x xs)

    goIndStep :: forall m n a. RevProps n -> Vector n a -> Vector ('Suc m) a -> Vector (n + 'Suc m) a
    goIndStep props accum (Cons x xs) = transportVS' @m @n (projR props) (go (indCaseN props) (Cons x accum) xs)


newtype Flip f x y = Flip { getFlip :: f y x }

transportVZ' :: forall n a. PlusZeroRight n -> Vector n a -> Vector (n + 'Zero) a
transportVZ' p v = getFlip (transport 
                            (eqSym (getPlusZeroRight p))
                            (Flip v))

transportVS' :: forall m n a. PlusSucRight n -> Vector ('Suc n + m) a -> Vector (n + 'Suc m) a
transportVS' p v = getFlip (transport 
                            (eqSym (getPlusSucRight p (Proxy :: Proxy m)))
                            (Flip v))
