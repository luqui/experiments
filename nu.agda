module nu where

import Level

data ν {l} (f : Set l -> Set l) : Set (Level.suc l) where
  Ana : ∀ {a : Set l} -> (a -> f a) -> a -> ν f

cata : ∀ {l} {f : Set l -> Set l} {a : Set l} -> (f a -> a) -> ν f -> a
cata f₁ (Ana x x₁) = ?