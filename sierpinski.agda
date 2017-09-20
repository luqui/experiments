{-# OPTIONS --without-K --copatterns #-}

module sierpinski where

open import HoTT

module Coprod-Facts {A B : Set} where
  SigmaRep = Σ Bool \{ false -> A ; true -> B }
  
  SigmaRep-is-set : is-set A -> is-set B -> is-set SigmaRep
  SigmaRep-is-set sa sb = Σ-level Bool-is-set
     (\{ true -> sb ; false -> sa })

  Coprod≃SigmaRep : (A ⊔ B) ≃ SigmaRep
  Coprod≃SigmaRep = to , is-eq to from 
                           (\{ (false , _) -> idp ; (true , _ ) -> idp }) 
                           (\{ (inl _) -> idp ; (inr _) -> idp })
    where
    to : A ⊔ B -> SigmaRep
    to (inl x) = false , x
    to (inr y) = true , y

    from : SigmaRep -> A ⊔ B
    from (false , x) = inl x
    from (true , y)  = inr y

  Coprod-is-set : is-set A -> is-set B -> is-set (A ⊔ B)
  Coprod-is-set sa sb = transport is-set (ua (Coprod≃SigmaRep ⁻¹)) (SigmaRep-is-set sa sb)

map-inr : ∀ {l m n} {A : Set l} {B : Set m} {C : Set n} -> (B -> C) -> A ⊔ B -> A ⊔ C
map-inr f (inl x) = inl x
map-inr f (inr y) = inr (f y)

g-sim-⊔ : {A A' B B' : Set} -> (A -> A' -> Set) -> (B -> B' -> Set) -> A ⊔ B -> A' ⊔ B' -> Set
g-sim-⊔ fA fB (inl x) (inl x') = fA x x'
g-sim-⊔ fA fB (inr y) (inr y') = fB y y'
g-sim-⊔ _ _ _ _ = ⊥


record Σ-Bisim {A B : Set} (f : A -> ⊤ ⊔ A) (g : B -> ⊤ ⊔ B) (x : A) (y : B) : Set where
  coinductive
  field
    next-sim : g-sim-⊔ _==_ (Σ-Bisim f g) (f x) (g y)
open Σ-Bisim

record PreΣ-Base : Set where
  coinductive
  field
    next-base : ⊤ ⊔ PreΣ-Base
open PreΣ-Base

PreΣ-Quot = SetQuot (Σ-Bisim next-base next-base)

next-quot : PreΣ-Quot -> ⊤ ⊔ PreΣ-Quot
next-quot s = SetQuot-rec (Coprod-Facts.Coprod-is-set ⊤-is-set SetQuot-is-set)
                          (map-inr q[_] ∘ next-base) lemma s
  where
  lemma : {a b : PreΣ-Base} -> Σ-Bisim next-base next-base a b 
        -> map-inr q[_] (next-base a) == map-inr q[_] (next-base b)
  lemma {a} {b} s with next-base a | next-base b | next-sim s
  ...                | inl x       | inl x'      | ns         
    = ap inl (contr-has-all-paths ⊤-is-contr _ _)
  ...                | inr y       | inr y'      | ns        
    = ap inr (quot-rel ns)
  lemma {a} {b} s    | inl _       | inr _       | ()
  lemma {a} {b} s    | inr _       | inl _       | ()

warmup : (b : PreΣ-Base) -> Σ-Bisim next-base next-base b b
next-sim (warmup b) with next-base b
...                              | inl t = idp
...                              | inr sim = {!!}
{-

quot-preserves-next : (b : PreΣ-Base) -> Σ-Bisim next-base next-quot b q[ b ]
next-sim (quot-preserves-next b) with next-base b
...                                 | inl t       = idp
...                                 | inr sim     = {!quot-preserves-next sim!}
-}

module Product where
  PreΣ : Set₁
  PreΣ = Σ Set (\A -> A × (A -> ⊤ ⊔ A))

  next : PreΣ -> ⊤ ⊔ PreΣ
  next (A , x , f) = map-inr (\x' -> A , x' , f) (f x)

{-

-}


{-
Product≃Corecord : Product.PreΣ ≃ Corecord.PreΣ
Product≃Corecord = to , is-eq to from to-from from-to
  where
  to-base' : {A : Set} -> (A -> ⊤ ⊔ A) -> A -> Corecord.PreΣ-Base
  Corecord.PreΣ-Base.next-base (to-base' f x) with f x
  ...                                            | inl t = inl t
  ...                                            | inr ts = inr (to-base' f ts)

  to-base : Product.PreΣ -> Corecord.PreΣ-Base
  to-base (A , x , f) = to-base' f x

  to : Product.PreΣ -> Corecord.PreΣ
  to s = q[ to-base s ]

  from : Corecord.PreΣ -> Product.PreΣ
  from s = Corecord.PreΣ , s , Corecord.next

  mutual
    to-base-preserves-next : ∀ p -> next to-base p

  to-from-lemma : ∀ base -> Corecord.PreΣ-Bisim (to-base (from q[ base ])) base
  Corecord.PreΣ-Bisim.next-sim (to-from-lemma base) = {!!}

  to-from : ∀ b -> to (from b) == b
  to-from b = SetQuot-elim {P = \q -> to (from q) == q} {!!} 
                 (\base -> quot-rel (to-from-lemma base))
                 {!!} b

  from-to : ∀ a -> from (to a) == a
  from-to (A , x , f) = {!!}

{-
PreΣSpace-≃-PreΣSpace' : PreΣSpace ≃ PreΣSpace'
PreΣSpace-≃-PreΣSpace' = to , is-eq to from {!!} {!!}
  where
  to : PreΣSpace -> PreΣSpace'
  to s = PreΣSpace , s , PreΣSpace.next

  from' : {A : Set} -> (A -> ⊤ ⊔ A) -> A -> PreΣSpace
  PreΣSpace.next (from' f s) with f s
  ...                           | inl tt = inl tt
  ...                           | inr a' = inr (from' f s)

  from : PreΣSpace' -> PreΣSpace
  from (A , (s , f)) = from' f s

  to-from : ∀ {b} -> to (from b) == b
  to-from = {!!}
-}
-}
