{-# OPTIONS --type-in-type --rewriting --without-K #-}

module lem-parametricity where

open import HoTT

module Coprod-Facts where
  swap : {A B : Set} -> A ⊔ B ≃ B ⊔ A
  swap = equiv swapf swapf swap-swap swap-swap
    where
    swapf : {A B : Set} -> A ⊔ B -> B ⊔ A
    swapf (inl a) = inr a
    swapf (inr b) = inl b
  
    swap-swap : {A B : Set} (x : A ⊔ B) -> swapf (swapf x) == x
    swap-swap (inl _) = idp
    swap-swap (inr _) = idp

  zero-right : {A : Set} -> A ⊔ ⊥ ≃ A
  zero-right {A} = equiv extract inl (\_ -> idp) (\{ (inl _) -> idp ; (inr ()) })
    where
    extract : A ⊔ ⊥ -> A
    extract (inl a) = a
    extract (inr ())

  zero-left : {A : Set} -> ⊥ ⊔ A ≃ A
  zero-left = zero-right ∘e swap

¬-equiv-⊥ : {A : Set} -> ¬ A -> A ≃ ⊥
¬-equiv-⊥ {A} ¬A = equiv ¬A from (\{ () }) from-to
  where
  from : ⊥ -> A
  from ()

  from-to : ∀ x -> from (¬A x) == x
  from-to a with ¬A a
  ...          | ()


LEM = (A : Set) -> is-prop A -> A ⊔ ¬ A

module LEM-Facts where
  LEM' = (A : Set) -> Trunc -1 (A ⊔ ¬ A)

  LEM-to-LEM' : LEM -> LEM'
  LEM-to-LEM' lem A with lem (Trunc -1 A) Trunc-level
  ...                  | inl x_ = Trunc-fmap inl x_
  ...                  | inr p = Trunc-fmap inr [ (\a -> ⊥-elim (p [ a ])) ]


  LEM-result-is-prop : {A : Set} -> LEM' -> is-prop A -> is-prop (A ⊔ ¬ A)
  LEM-result-is-prop {A} lem' A-is-prop = Trunc-elim (\_ -> is-prop-is-prop) helper (lem' A)
    where
    coprod-equiv-left : {A B : Set} -> ¬ B -> A ≃ (A ⊔ B)
    coprod-equiv-left {A} {B} ¬B = transport! (\ □ -> A ≃ (A ⊔ □)) (ua (¬-equiv-⊥ ¬B)) (Coprod-Facts.zero-right ⁻¹)

    helper : A ⊔ ¬ A -> is-prop (A ⊔ ¬ A)
    helper (inl a) = transport is-prop (ua (coprod-equiv-left (λ ¬A → ¬A a))) A-is-prop
    helper (inr ¬a) = transport is-prop (ua (Coprod-Facts.swap ∘e coprod-equiv-left {¬ A} {A} ¬a)) ¬-is-prop

  LEM'-to-LEM : LEM' -> LEM
  LEM'-to-LEM lem' A A-is-prop = Trunc-elim (\_ -> LEM-result-is-prop lem' A-is-prop) (idf _) (lem' A)

  LEM-≃-LEM' : LEM ≃ LEM'
  LEM-≃-LEM' = equiv LEM-to-LEM' LEM'-to-LEM 
                     (\lem' -> λ= (\_ -> fst (Trunc-level {n = -1} _ _))) 
                     (\lem -> λ= (\A -> λ= (\A-is-prop -> fst (LEM-result-is-prop (LEM-to-LEM' lem) A-is-prop _ _))))


-- HoTT book exercise 6.9
module Nonparametric (lem : LEM) where
  swap : Bool ≃ Bool
  swap = Coprod-Facts.swap

  not : Bool -> Bool
  not = –> swap

  swap≠ide : ¬ (swap == ide Bool)
  swap≠ide p = Bool-false≠true (ap (\f -> –> f true) p)

  Inspect : {A B : Set} -> (f : A -> B) -> A -> Set
  Inspect {_} {B} f x = Σ B (\y -> f x == y)

  inspect : {A B : Set} -> (f : A -> B) -> (x : A) -> Inspect f x
  inspect f x = f x , idp

  equiv= : {A B : Set} -> (e e' : A ≃ B) -> (–> e == –> e') -> e == e'
  equiv= (f , f-is-equiv) (.f , f-is-equiv') idp = pair= idp (prop-has-all-paths is-equiv-is-prop _ _)

  two-Bool-equivs : (e : Bool ≃ Bool) -> (e == ide Bool) ⊔ (e == swap)
  two-Bool-equivs e with inspect (–> e) true | inspect (–> e) false
  ...                 | true , p            | true , q  = ⊥-elim (Bool-true≠false (–>-is-inj e _ _ (p ∙ ! q)))
  ...                 | true , p            | false , q = inl (equiv= _ _ (λ= \{ true -> p ; false -> q }))
  ...                 | false , p           | true , q  = inr (equiv= _ _ (λ= \{ true -> p ; false -> q }))
  ...                 | false , p           | false , q = ⊥-elim (Bool-true≠false (–>-is-inj e _ _ (p ∙ ! q)))

  Bool-equiv-is-swap : (e : Bool ≃ Bool) -> e ≠ ide Bool -> e == swap
  Bool-equiv-is-swap e p with two-Bool-equivs e
  ...                       | inl iside = ⊥-elim (p iside)
  ...                       | inr isswap = isswap

  NontrivialAutomorphism : Set -> Set
  NontrivialAutomorphism X = Σ (X ≃ X) (\e -> ¬ (e == ide X))

  NontrivialAutomorphism-preserve : {X Y : Set} -> X ≃ Y -> NontrivialAutomorphism X -> NontrivialAutomorphism Y
  NontrivialAutomorphism-preserve X≃Y auto with ua X≃Y
  ...                                           | idp = auto

  swap-NTA : NontrivialAutomorphism Bool
  swap-NTA = swap , swap≠ide

  NTA-determine : {X : Set} (a b : NontrivialAutomorphism X) -> fst a == fst b -> a == b
  NTA-determine (a , p) (.a , p') idp = pair= idp (prop-has-all-paths (Π-level (\_ -> ⊥-is-prop)) p p')

  swap-NTA-unique : (a : NontrivialAutomorphism Bool) -> a == swap-NTA
  swap-NTA-unique (a , p) with two-Bool-equivs a
  ...                        | inl iside = ⊥-elim {lzero} {\_ -> (a , p) == swap-NTA} (p iside)
  ...                        | inr isswap = NTA-determine _ _ isswap 

  NTA-Bool-is-contr : is-contr (NontrivialAutomorphism Bool)
  NTA-Bool-is-contr = swap-NTA , ! ∘ swap-NTA-unique

  key : {X : Set} -> Trunc -1 (X ≃ Bool) -> is-contr (NontrivialAutomorphism X)
  key = Trunc-elim (\_ -> is-contr-is-prop) (\e -> transport! (\ □ -> is-contr (NontrivialAutomorphism □)) (ua e) NTA-Bool-is-contr) 

  exercise : (X : Set) -> X -> X
  exercise X with lem (Trunc -1 (X ≃ Bool)) Trunc-level
  ...           | inl e = –> (fst (fst (key e)))
  ...           | inr ne = idf X

  exercise-proof : exercise Bool == not
  exercise-proof with lem (Trunc -1 (Bool ≃ Bool)) Trunc-level
  ...           | inl e = ap (–>) (Bool-equiv-is-swap _ (snd (fst (key e))))
  ...           | inr ne with ne [ ide Bool ]
  ...                       | ()
