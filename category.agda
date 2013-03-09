{-# OPTIONS --type-in-type #-}

module category where


record Category : Set where
  field
    Obj   : Set
    Hom   : Obj -> Obj -> Set
    _/_o_ : forall {A B C} -> Hom B C -> Hom A B -> Hom A C


open Category


record Functor (C D : Category) : Set where
  field
    FObj   : Obj C -> Obj D
    FHom   : {A B : Obj C} -> Hom C A B -> Hom D (FObj A) (FObj B)

open Functor


data _≡_ {A : Set} : A -> A -> Set where 
  refl : {x : A} -> x ≡ x

-- The category of agda types w/ functions
Agda : Category
Agda = 
  record { Obj   = Set
         ; Hom   = \A B -> A -> B
         ; _/_o_ = \f g x -> f (g x)
         }

-- The category of categories w/ functors
Cat : Category
Cat =
  record { Obj = Category
         ; Hom = Functor
         ; _/_o_ = \f g -> 
             record { FObj = \x -> FObj f (FObj g x)
                    ; FHom = \m -> FHom f (FHom g m)
                    }
         }

-- The category of functors w/ natural transformations
_~>_ : Category -> Category -> Category
C ~> D =
  record { Obj   = Functor C D
         ; Hom   = \F G -> (x : Obj C) -> Hom D (FObj F x) (FObj G x)
         ; _/_o_ = \f g x -> D / f x o g x
         }

-- The category of endofunctors on C
Endo : (C : Category) -> Category
Endo C = C ~> C

composeDiscrete : {A : Set} {x y z : A} -> y ≡ z -> x ≡ y -> x ≡ z
composeDiscrete refl refl = refl

-- The discrete category on a Set
Discrete : (A : Set) -> Category
Discrete A =
  record { Obj = A
         ; Hom = \x y -> x ≡ y
         ; _/_o_ = composeDiscrete
         }



-- The identity functor
I : {C : Category} -> Hom Cat C C 
I = record { FObj = \x -> x ; FHom = \f -> f } 


-- Product
record Products {C : Category} : Set where
  field
    _⊗_ : Obj C -> Obj C -> Obj C
    ⟨_,_⟩ : forall {X₁ X₂ Y} -> Hom C Y X₁ -> Hom C Y X₂ -> Hom C Y (X₁ ⊗ X₂)
    π₁ : forall {X₁ X₂} -> Hom C (X₁ ⊗ X₂) X₁
    π₂ : forall {X₁ X₂} -> Hom C (X₁ ⊗ X₂) X₂

-- Monads
record Monad (C : Category) : Set where
  field
    T    : Obj (Endo C)
    unit : Hom (Endo C) I T
    join : Hom (Endo C) (Cat / T o T) T


-- We have phrased Monad in terms of Objs and Homs -- but if we can make
-- all the fields of a structure Objs of various categories, then we can
-- automatically derive the morphisms for that structure; i.e. we can
-- automatically find a category of such structures.

-- If you use the discrete category, then the structure's category will
-- be discrete -- i.e. admit no nontrivial morphisms.