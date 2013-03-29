{-# OPTIONS --type-in-type #-}

module category where


record Category : Set where
  field
    Obj   : Set
    Hom   : Obj -> Obj -> Set
    id    : (A : Obj) -> Hom A A 
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
         ; id    = \_ x -> x
         ; _/_o_ = \f g x -> f (g x)
         }

-- The category of categories w/ functors
Cat : Category
Cat =
  record { Obj = Category
         ; Hom = Functor
         ; id  = \_ -> record { FObj = id Agda _
                              ; FHom = id Agda _
                              }
         ; _/_o_ = \f g -> 
             record { FObj = \x -> FObj f (FObj g x)
                    ; FHom = \m -> FHom f (FHom g m)
                    }
         }

data Zero : Set where

absurd : {A : Set} -> Zero -> A
absurd ()

C0 : Category
C0 = 
  record { Obj = Zero
         ; Hom = \{ () () }
         ; id = {!!}
         ; _/_o_ = \{x} -> absurd x
         }

data One : Set where
  one : One

C1 : Category
C1 = 
  record { Obj = One
         ; Hom = \{one one -> One}
         ; id = \{one -> one}
         ; _/_o_ = \{ {one} {one} {one} one one -> one}
         }

data Two : Set where
  one2 : Two
  two2 : Two

data TwoHom : Two -> Two -> Set where
  idOne2 : TwoHom one2 one2
  idTwo2 : TwoHom two2 two2
  oneTwo2 : TwoHom one2 two2

C2 : Category
C2 =
  record { Obj = Two
         ; Hom = TwoHom
         ; id = \{one2 -> idOne2 ; two2 -> idTwo2 }
         ; _/_o_ = \{ {one2} {one2} {one2} idOne2 idOne2  -> idOne2
                    ; {one2} {one2} {two2} oneTwo2 idOne2 -> oneTwo2
                    ; {one2} {two2} {two2} idTwo2 oneTwo2 -> oneTwo2
                    ; {two2} {two2} {two2} idTwo2 idTwo2  -> idTwo2
                    }
         }

-- The category of functors w/ natural transformations
_~>_ : Category -> Category -> Category
C ~> D =
  record { Obj   = Functor C D
         ; Hom   = \F G -> (x : Obj C) -> Hom D (FObj F x) (FObj G x)
         ; id    = \_ x -> id D _
         ; _/_o_ = \f g x -> D / f x o g x
         }

-- The category of endofunctors on C
Endo : (C : Category) -> Category
Endo C = C ~> C

composeDiscrete : {A : Set} {x y z : A} -> y ≡ z -> x ≡ y -> x ≡ z
composeDiscrete refl refl = refl

-- The constant functor
Δ : (C : Category) -> {D : Category} -> (d : Obj D) -> Obj (C ~> D)
Δ C {D} d = 
  record { FObj = \c -> d
          ; FHom = \f -> id D _
          }

-- The discrete category on a Set
Discrete : (A : Set) -> Category
Discrete A =
  record { Obj = A
         ; Hom = \x y -> x ≡ y
         ; id  = \_ -> refl
         ; _/_o_ = composeDiscrete
         }



-- The identity functor
I : {C : Category} -> Hom Cat C C 
I = record { FObj = \x -> x ; FHom = \f -> f } 


-- Product
record Products (C : Category) : Set where
  field
    _⊗_ : Obj C -> Obj C -> Obj C
    ⟨_,_⟩ : forall {X₁ X₂ Y} -> Hom C Y X₁ -> Hom C Y X₂ -> Hom C Y (X₁ ⊗ X₂)
    π₁ : forall {X₁ X₂} -> Hom C (X₁ ⊗ X₂) X₁
    π₂ : forall {X₁ X₂} -> Hom C (X₁ ⊗ X₂) X₂

_/_⊗_ = Products._⊗_
_/⟨_,_⟩ = Products.⟨_,_⟩ 

_/_×_ : {C : Category} -> (P : Products C) -> {X X′ Y Y′ : Obj C} -> Hom C X X′ -> Hom C Y Y′ -> Hom C (P / X ⊗ Y) (P / X′ ⊗ Y′)
_/_×_ {C} P f g = P /⟨ C / f o Products.π₁ P , C / g o Products.π₂ P ⟩

data Prod (A B : Set) : Set where
  prod : A -> B -> Prod A B

AgdaProducts : Products Agda
AgdaProducts = 
  record { _⊗_ = Prod
         ; ⟨_,_⟩ = \f g x -> prod (f x) (g x)
         ; π₁ = \{ (prod x _) -> x }
         ; π₂ = \{ (prod _ y) -> y }
         }

CatProducts : Products Cat
CatProducts =
  record { _⊗_ = \C D -> record { Obj = Prod (Obj C) (Obj D)
                                ; Hom = \{(prod c d) (prod c′ d′) -> Prod (Hom C c c′) (Hom D d d′)}
                                ; id = \{(prod c d) -> prod (id C c) (id D d)}
                                ; _/_o_ = \{ {prod _ _} {prod _ _} {prod _ _} 
                                             (prod gc gd) (prod fc fd) -> prod (C / gc o fc) (D / gd o fd)}
                                }
         ; ⟨_,_⟩ = \F G -> record { FObj = \y -> prod (FObj F y) (FObj G y)
                                 ; FHom = \f -> prod (FHom F f) (FHom G f)
                                 }
         ; π₁ = record { FObj = \{(prod A _) -> A}
                       ; FHom = \{ {prod _ _} {prod _ _} (prod f _) -> f } 
                       }
         ; π₂ = record { FObj = \{(prod _ B) -> B}
                       ; FHom = \{ {prod _ _} {prod _ _} (prod _ g) -> g }
                       }
         }

-- Now, with CatProducts, we can give my own natural transformation defintiion:

-- A natural transformation T is a functor C ⊗ 2 -> D.  The typical F and G : C -> D
-- can be recovered as 
-- F = T o (× 0)
-- G = T o (× 1)

_~>·_ : (C D : Category) -> Set
C ~>· D = Functor (CatProducts / C ⊗ C2) D



FunctorProducts : {C D : Category} -> Products D -> Products (C ~> D)
FunctorProducts Pd =
  record { _⊗_ = \F G -> record { FObj = \X -> Pd / FObj F X ⊗ FObj G X
                                 ; FHom = \f -> Pd / FHom F f × FHom G f
                                 }
         ; ⟨_,_⟩ = \t t′ x -> Pd /⟨ t x , t′ x ⟩
         ; π₁ = \x -> Products.π₁ Pd
         ; π₂ = \x -> Products.π₂ Pd
         }

-- The category of isomorphisms in a given category
Iso : Obj (Cat ~> Cat)
Iso = 
  record { FObj = \C -> 
                record { Obj = Obj C
                       ; Hom = \A B -> Prod (Hom C A B) (Hom C B A)
                       ; id = \_ -> prod (id C _) (id C _)
                       ; _/_o_ = \{(prod g g′) (prod f f′) -> prod (C / g o f) (C / f′ o g′) }
                }
         ; FHom = \F -> 
                record { FObj = FObj F
                       ; FHom = \{(prod f f′) -> prod (FHom F f) (FHom F f′) }
                       }
         }


record Exponentials {C : Category} (P : Products C) : Set where
  field
    _⟶_ : Obj C -> Obj C -> Obj C
    curry : {X Y Z : Obj C} -> Hom C (P / X ⊗ Y) Z -> Hom C X (Y ⟶ Z)
    uncurry : {X Y Z : Obj C} -> Hom C X (Y ⟶ Z) -> Hom C (P / X ⊗ Y) Z

AgdaExponentials : Exponentials AgdaProducts
AgdaExponentials =
  record { _⟶_ = \X Y -> X -> Y
         ; curry = \f x y -> f (prod x y)
         ; uncurry = \{f (prod x y) -> f x y}
         }

-- Monads
record Monad (C : Category) : Set where
  field
    T    : Obj (Endo C)
    unit : Hom (Endo C) I T
    join : Hom (Endo C) (Cat / T o T) T



record Algebra {C : Category} (F : Obj (Endo C)) : Set where
  field
    A : Obj C
    alg : Hom C (FObj F A) A

Alg : {C : Category} (F : Obj (Endo C)) -> Category
Alg {C} F = 
  record { Obj = Algebra F
         ; Hom = \a b -> Hom C (Algebra.A a) (Algebra.A b)
         ; id  = \_ -> id C _
         ; _/_o_ = \g f -> C / g o f
         }


-- We have phrased Monad in terms of Objs and Homs -- but if we can make
-- all the fields of a structure Objs of various categories, then we can
-- automatically derive the morphisms for that structure; i.e. we can
-- automatically find a category of such structures.

-- If you use the discrete category, then the structure's category will
-- be discrete -- i.e. admit no nontrivial morphisms.