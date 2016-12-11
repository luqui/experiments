{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeInType, GADTs, TypeOperators, RankNTypes, TypeFamilies, UndecidableInstances, TypeApplications, ScopedTypeVariables, AllowAmbiguousTypes, NoMonomorphismRestriction #-}

import Data.Kind (Type)

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

type family (+) a b :: Nat where
    'Zero + b = b
    'Suc a + b = 'Suc (a + b)
  
class IsNat (n :: Nat) where
    natRec :: p 'Zero -> (forall m. p m -> p ('Suc m)) -> p n
instance IsNat 'Zero where natRec z _ = z
instance IsNat n => IsNat ('Suc n) where natRec z s = s (natRec z s)

plusZeroRight :: IsNat n => (n + 'Zero) == n
plusZeroRight = getPZR_Recursor $ natRec base inductive
    where
    base :: PZR_Recursor 'Zero
    base = PZR_Recursor Refl
    inductive :: PZR_Recursor n -> PZR_Recursor ('Suc n)
    inductive (PZR_Recursor Refl) = PZR_Recursor Refl
newtype PZR_Recursor n = PZR_Recursor { getPZR_Recursor :: (n + 'Zero) == n }

plusSucRight :: forall m n. IsNat n => (n + 'Suc m) == 'Suc (n + m) 
plusSucRight = getPZS_Recursor @ m @ n (natRec base inductive)
    where
    base :: forall a. PZS_Recursor a 'Zero
    base = PZS_Recursor Refl
    inductive :: forall a b. PZS_Recursor a b -> PZS_Recursor a ('Suc b)
    inductive (PZS_Recursor Refl) = PZS_Recursor Refl

newtype PZS_Recursor m n = PZS_Recursor { getPZS_Recursor :: (n + 'Suc m) == 'Suc (n + m) }


data Vector :: Nat -> Type -> Type where
    Nil :: forall a. Vector 'Zero a
    Cons :: forall n a. a -> Vector n a -> Vector ('Suc n) a

appendV :: Vector n a -> Vector m a -> Vector (n+m) a
appendV Nil ys = ys
appendV (Cons x xs) ys = Cons x (appendV xs ys)

zipV :: Vector n a -> Vector n b -> Vector n (a,b)
zipV Nil Nil = Nil
zipV (Cons x xs) (Cons y ys) = Cons (x,y) (zipV xs ys)


reverseV :: Vector n a -> Vector n a
reverseV = go Nil
    where
    go :: forall m n a. (IsNat m) => Vector m a -> Vector n a -> Vector (m+n) a
    go accum Nil = transportVZ' accum
    go accum (Cons x xs) = goIndStep accum (Cons x xs)

    goIndStep :: forall m n a. (IsNat m) => Vector m a -> Vector ('Suc n) a -> Vector (m + 'Suc n) a
    goIndStep accum (Cons x xs) = transportVS' @ n @ m (go (Cons x accum) xs)

newtype Flip f x y = Flip { getFlip :: f y x }

transportVZ' :: forall n a. (IsNat n) => Vector n a -> Vector (n + 'Zero) a
transportVZ' v = getFlip (transport 
                          (eqSym plusZeroRight)
                          (Flip v))

transportVS' :: forall m n a. (IsNat n) => Vector ('Suc n + m) a -> Vector (n + 'Suc m) a
transportVS' v = getFlip (transport 
                          (eqSym (plusSucRight @ m @ n))
                          (Flip v))
