import Data.Unamb
import Data.Lub


data Nat = Zero | Succ Nat
    deriving Show

instance HasLub Nat where
    lub a b = unambs [
                  case a of 
                      Zero -> Zero
                      Succ _ -> Succ (pa `lub` pb),
                  case b of
                      Zero -> Zero
                      Succ _ -> Succ (pa `lub` pb)
              ]
        where
        Succ pa = a
        Succ pb = b
    
instance Num Nat where
    x + Zero = x
    x + Succ y = Succ (x + y)

    x * Zero = Zero
    x * Succ y = x + x * y

    abs = id
    signum Zero = Zero
    signum (Succ x) = Succ Zero

    negate _ = Zero

    fromInteger 0 = Zero
    fromInteger n = Succ (fromInteger (n-1))

laxPlus :: (Num a) => a -> a -> a
laxPlus a b = (a + b) `unamb` (b + a)

laxPlus' :: Nat -> Nat -> Nat
laxPlus' a b = (a + b) `lub` (b + a)

laxPlus'' :: Nat -> Nat -> Nat
laxPlus'' a b = lubs [
    case a of 
        Zero -> b
        Succ _ -> r,
    case b of
        Zero -> a
        Succ _ -> r
    ]
    where
    Succ pa = a
    Succ pb = b
    r = Succ ((pa `laxPlus''` b) `lub` (a `laxPlus''` pb))

leastStrict :: (HasLub a) => (a -> a -> a) -> (a -> a -> a)
leastStrict f x y = f x y `lub` f y x

laxMult :: Nat -> Nat -> Nat
laxMult a b = lubs [
        case a of 
            Zero -> Zero
            Succ _ -> r,
        case b of
            Zero -> Zero
            Succ _ -> r
    ]
    where
    Succ pa = a
    Succ pb = b
    r = (b `laxPlus''` (pa `laxMult` b)) `lub` (a `laxPlus''` (a `laxMult` pb))

atLeast :: Nat -> Nat
atLeast Zero = undefined
atLeast (Succ n) = Succ (atLeast n)
