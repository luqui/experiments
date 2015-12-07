{-# LANGUAGE TypeOperators, GeneralizedNewtypeDeriving #-}

import Data.Void
import Data.Function (fix)
import Data.Unamb (unamb)
import Control.Category
import Prelude hiding (id, (.))

data Sigma = T
    deriving Show

class LinearDomain a where
    bot :: a
    top :: a
    (\/) :: a -> a -> a
    (/\) :: a -> a -> a

instance LinearDomain Sigma where
    bot = error "Sigma.bottom"
    top = T
    (\/) = unamb
    (/\) = seq

instance LinearDomain Void where
    bot = error "Void.bottom"
    top = error "Void.top"
    (\/) = error "Void.\\/"
    (/\) = error "Void./\\"

forAll :: (LinearDomain a) => (a -> Sigma) -> Sigma
forAll p = p bot

forSome :: (LinearDomain a) => (a -> Sigma) -> Sigma
forSome p = p top


data S a = S a
    deriving (Show)

instance (LinearDomain a) => LinearDomain (S a) where
    bot = error "S.bottom"
    top = S top
    a \/ b = let S a' = a; S b' = b in (a `unamb` b) `seq` S (a' \/ b')
    S a /\ S b = S (a /\ b)

hat :: a -> S a
hat = S


newtype Flip a = Flip (a -> Sigma)

applyFlip :: Flip a -> a -> Sigma
applyFlip (Flip x) = x

instance (LinearDomain a) => LinearDomain (Flip a) where
    bot = Flip (const bot)
    top = Flip (const top)
    Flip f \/ Flip g = Flip (\x -> f x \/ g x)
    Flip f /\ Flip g = Flip (\x -> f x /\ g x)


newtype N = N (S N)
    deriving (Show, LinearDomain, ObserveBot)

atLeast :: Integer -> N -> Sigma
atLeast 0 _ = top
atLeast n (N (S a)) = atLeast (n-1) a

-- There is one element below top in Flip (Flip N)
predTopFFN :: Flip (Flip N)
predTopFFN = Flip (\(Flip c) -> c top)


newtype Omega = Omega (Flip Omega)
    deriving (LinearDomain, ObserveTop, ObserveBot)

inward :: Omega -> Omega
inward w = Omega (Flip (\(Omega (Flip f)) -> f w))


-- Gives top only when input is top, otherwise bot
class (LinearDomain a) => ObserveTop a where
    observeTop :: a -> Sigma

-- Gives bot only when input is bot, otherwise top
class (LinearDomain a) => ObserveBot a where
    observeBot :: a -> Sigma

instance ObserveTop Sigma where observeTop T = top
instance ObserveBot Sigma where observeBot T = top

instance (LinearDomain a) => ObserveBot (S a) where observeBot (S _) = top
instance (ObserveTop a) => ObserveTop (S a) where observeTop (S a) = observeTop a

instance (LinearDomain a) => ObserveTop (Flip a) where observeTop (Flip f) = f bot
instance (LinearDomain a) => ObserveBot (Flip a) where observeBot (Flip f) = f top

-- Adding a domain on top of another.
-- Invariant: either b is bot or a is top
-- Also we consider Plus bot bot = bot.
data a +> b = Plus a b
    deriving Show

-- Two different smart constructors that enforce the invariant in different ways.
-- mkPlus adjusts b to match a, mkPlus' adjusts a to match b.
mkPlus :: (ObserveTop a, LinearDomain b) => a -> b -> a +> b
mkPlus a b = Plus a ((observeTop a `seq` top) /\ b)

mkPlus' :: (LinearDomain a, ObserveBot b) => a -> b -> a +> b
mkPlus' a b = Plus ((observeBot b `seq` top) \/ a) b

inl :: (LinearDomain b) => a -> a +> b
inl x = Plus x bot

inr :: (LinearDomain a) => b -> a +> b
inr y = Plus top y

instance (LinearDomain a, LinearDomain b) => LinearDomain (a +> b) where
    bot = Plus bot bot
    top = Plus top top
    ~(Plus a b) \/ ~(Plus a' b') = Plus (a \/ a') (b \/ b')
    ~(Plus a b) /\ ~(Plus a' b') = Plus (a /\ a') (b /\ b')

instance (ObserveTop a, ObserveTop b) => ObserveTop (a +> b) where
    -- We would just say observeTop b, but _|_ = T for Void, so 
    -- if b :: Void, then b could = top and a might not be
    observeTop (Plus a b) = observeTop a /\ observeTop b

instance (ObserveBot a, ObserveBot b) => ObserveBot (a +> b) where
    -- We would just say observeBot a, but _|_ = T for Void, so
    -- if a :: Void, then a could = bot and b could still be defined
    observeBot (Plus a b) = observeBot a /\ observeBot b


-- LD-isomorphisms

data a =~= b = Iso (a -> b) (b -> a)

instance Category (=~=) where
    id = Iso id id
    Iso f g . Iso f' g' = Iso (f . f') (g' . g)

inverse :: a =~= b -> b =~= a
inverse (Iso f g) = Iso g f

(%) :: a =~= b -> a -> b
Iso f _ % x = f x


iso_N_SN :: N =~= S N
iso_N_SN = Iso S N

iso_Plus_Assoc :: ((a +> b) +> c) =~= (a +> (b +> c))
iso_Plus_Assoc = Iso forward backward
    where
    forward ~(Plus ~(Plus a b) c) = Plus a (Plus b c)
    backward ~(Plus a ~(Plus b c)) = Plus (Plus a b) c

iso_S_SigPlus :: S a =~= (Sigma +> a)
iso_S_SigPlus = Iso (\(S x) -> inr x) (\(Plus a b) -> a `seq` S b)

iso_NSig_FFN :: (N +> Sigma) =~= Flip (Flip N)
iso_NSig_FFN = Iso forward backward
    where
    forward ~(Plus n sig) = Flip (\(Flip c) -> observeTop sig \/ c n)
    backward (Flip c) = (observeTop (Flip c) `seq` top) \/ inl (go 1)
        where
        go n = c (Flip (atLeast n)) `seq` N (S (go (n+1)))

-- succFN _|_ = _|_
-- succFN top = top
succFN :: Flip N -> Flip N
succFN f = Flip (\n -> applyFlip f (N (S n)))

succFFN :: Flip (Flip N) -> Flip (Flip N)
succFFN f = Flip (\n -> applyFlip f (succFN n))
