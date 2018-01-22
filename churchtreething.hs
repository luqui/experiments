{-# LANGUAGE RankNTypes #-}

import Data.Tuple (swap)
import Control.Arrow (first, second)
import Debug.Trace

type Nat = Integer

newtype CTS = CTS { getCTS :: forall a. ((a -> a) -> a) -> a }

fpow :: Nat -> (a -> a) -> (a -> a)
fpow 0 _ = id
fpow n f = f . fpow (n-1) f

pairToCTS :: (Nat, Nat) -> CTS
pairToCTS (m, n) = CTS $ \f -> fpow m (f . const) . f $ fpow n (f . const)

data Tree = P | Q | F Tree Tree
    deriving Show

ctsToTree :: CTS -> Tree
ctsToTree c = getCTS c (\e -> F (e P) (e Q))

ctsToPair :: CTS -> (Nat, Nat)
ctsToPair c = getCTS c (\e -> f' (e (1,0)) (e (0,1)))
    where
    f p q | p == q      = first succ p
          | (x,0) <- p
          , (y,1) <- q
          , x == y + 1  = (0, y)
          | otherwise   = error $ "Function not defined on " ++ show (p,q)

    --f' p q = trace ("f " ++ show p ++ " " ++ show q ++ " = " ++ show r) r
    --    where r = f p q
    f' = f

-- Strangely this seems to work.  Djest can't find any counterexamples.


{-
ctsToPair :: CTS -> (Nat, Nat)

-- ctsToPair (pairToCTS (0,0)) = (0,0)
-- ctsToPair (CTS $ \f -> f id) = (0,0)
--      (\e -> F (e P) (e Q)) id
--    = F (id P) (id Q)
--    = F P Q
--
-- ctsToPair (CTS $ \f -> f (f . const)) = (0,1)
--      let f = \e -> F (e P) (e Q)
--      f (f . const)
--    = (\e -> F (e P) (e Q)) (f . const)
--    = F ((f . const) P) ((f . const) Q)
--    = F (f (const P)) (f (const Q))
--    = F ((\e -> F (e P) (e Q)) (const P)) ((\e -> F (e P) (e Q)) (const Q))
--    = F (F (const P P) (const P Q)) (F (const Q P) (const Q Q))
--    = F (F P P) (F Q Q)
--
-- ctsToPair (CTS $ \f -> f . const . f $ id) = (1,0)
--      let f = \e -> F (e P) (e Q)
--      (f . const . f) id
--    = f (const (f id))
--    = (\e -> F (e P) (e Q)) (const (f id))
--    = F (const (f id) P) (const (f id) Q)
--    = F (f id) (f id)
--    = F ((\e -> F (e P) (e Q)) id) ((\e -> F (e P) (e Q)) id)
--    = F (F (id P) (id Q)) (F (id P) (id Q))
--    = F (F P Q) (F P Q)

ctsToPair c = getCTS c $ \e ->  -- e :: (Nat, Nat) -> (Nat, Nat)
    e (0,0)
-}
{-
A0 = f id                                       = (0, 0)

B0 = (f . const) A0
   = f . const . f $ id                         = (1, 0)
B1 = f $ f . const                              = (0, 1)

C0 = (f . const) B0
   = f . const . f . const . f $ id             = (2, 0)
C1 = (f . const) B1
   = f . const . f $ f . const                  = (1, 1)
C2 = f $ f . const . f . const                  = (0, 2)

D0 = (f . const) C0
   = f . const . f . const . f . const . f $ id = (3, 0)
D1 = (f . const) C1
   = f . const . f . const . f $ f . const      = (2, 1)
D2 = (f . const) C2
   = f . const . f $ f . const . f . const      = (1, 2)
D3 = f $ f . const . f . const . f . const      = (0, 3)

-}
