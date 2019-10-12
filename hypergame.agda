{-# OPTIONS --type-in-type #-}

module hypergame where

open import Relation.Binary.PropositionalEquality
open import Data.Empty

data Game : Set where
    game : {M : Set} -> (M -> Game) -> Game

hypergame : Game
hypergame = game {Game} (\m -> m)

RecP : (Game -> Set) -> Game -> Set
RecP P (game {M} t) = (m : M) -> P (t m)

module Rec (P : Game -> Set) (e : (g : Game) -> RecP P g -> P g) where
  builder : (g : Game) -> RecP P g
  builder (game t) m = e (t m) (builder (t m))

  rec : (g : Game) -> P g
  rec g = e g (builder g)

elim-hypergame : ⊥
elim-hypergame = Rec.rec (\g -> g ≡ hypergame -> ⊥) (\{ .hypergame r refl -> r hypergame refl }) hypergame refl
