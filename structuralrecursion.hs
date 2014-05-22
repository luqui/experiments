{-# LANGUAGE DeriveFunctor, ExistentialQuantification #-}

-- A structurally recursive function f :: [a] -> b is isomorphic to a list
-- fold, which can be incrementalized as (a -> b -> b, b).  Any function which
-- consumes [a] in a structurally recursive way (but does not necessarily use its
-- own result recursively) can be incrementalized on the structural part; that is:
-- ∃ s. (a -> s -> s, s, s -> b)

-- We generalize this to any recursive structure

newtype Mu f = Roll { unroll :: f (Mu f) }

-- MF b = mu function = Mu f -> b
data MF f b = forall s. MF (f s -> s) (s -> b)

