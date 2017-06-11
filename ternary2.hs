{-# LANGUAGE DataKinds, RankNTypes, PolyKinds, DefaultSignatures #-}

data BitPos = Half BitPos

data Trit b = TA | TB | TC
    deriving (Enum, Bounded, Eq, Ord)
data HalfTrit b = HA | HB
    deriving (Enum, Bounded, Eq, Ord)
data Zero b = ZA
    deriving (Enum, Bounded, Eq, Ord)

instance Show (Trit b) where
    show TA = "A"
    show TB = "B"
    show TC = "C"

instance Show (HalfTrit b) where
    show HA = "A"
    show HB = "B"

instance Show (Zero b) where
    show ZA = "A"

class Interp a where
    interp :: a b -> Rational

instance Interp Trit where
    interp TA = 0
    interp TB = 1/2
    interp TC = 1

instance Interp HalfTrit where
    interp HA = 0
    interp HB = 1/2

instance Interp Zero where
    interp ZA = 0

class HasZero a where
    zero :: a b

instance HasZero Trit where zero = TA
instance HasZero HalfTrit where zero = HA
instance HasZero Zero where zero = ZA

class Finite a where
    enum :: [a b]
    default enum :: (Enum (a b), Bounded (a b)) => [a b]
    enum = [minBound..maxBound]

instance Finite Trit
instance Finite HalfTrit
instance Finite Zero

prop_adder :: 
    (Interp f, Interp g, Interp h, Interp h')
    => (forall b. f (Half b) -> g (Half b) -> (h b, h' (Half b)))
    -> f (Half b) -> g (Half b) -> Bool
prop_adder adder x y = 
    let (z, carry) = adder x y in
    interp x + interp y == 2*interp z + interp carry

check_adder ::
    (Interp f, Finite f, Interp g, Finite g, Interp h, Interp h')
    => (forall b. f (Half b) -> g (Half b) -> (h b, h' (Half b)))
    -> Bool
check_adder adder = and [ prop_adder adder x y | x <- enum, y <- enum ]

adder1 :: Trit (Half b) -> Trit (Half b) -> (Trit b, HalfTrit (Half b))
adder1 TA TA = (TA, HA)
adder1 TA TB = (TA, HB)
adder1 TA TC = (TB, HA)
adder1 TB TB = (TB, HA)
adder1 TB TC = (TB, HB)
adder1 TC TC = (TC, HA)
adder1 x y = adder1 y x


adder2 :: Trit (Half b) -> HalfTrit (Half b) -> (HalfTrit b, HalfTrit (Half b))
adder2 TA HA = (HA, HA)
adder2 TA HB = (HA, HB)
adder2 TB HA = (HA, HB)
adder2 TB HB = (HB, HA)
adder2 TC HA = (HB, HA)
adder2 TC HB = (HB, HB)


adder3 :: HalfTrit (Half b) -> HalfTrit (Half b) -> (Zero b, Trit (Half b))
adder3 HA HA = (ZA, TA)
adder3 HA HB = (ZA, TB)
adder3 HB HA = (ZA, TB)
adder3 HB HB = (ZA, TC)


promote :: HalfTrit b -> Trit b
promote HA = TA
promote HB = TB


infixr 5 :>
data R f b = f b :> R f (Half b)


addReals1 :: R Trit (Half b) -> R Trit (Half b) -> (R Trit b, R HalfTrit (Half b))
addReals1 (x :> xs) (y :> ys) = 
    let (z, carry) = adder1 x y
        (zs, carries) = addReals1 xs ys
    in (z :> zs, carry :> carries)

addReals2 :: R Trit (Half b) -> R HalfTrit (Half b) -> (R HalfTrit b, R HalfTrit (Half b))
addReals2 (x :> xs) (y :> ys) = 
    let (z, carry) = adder2 x y
        (zs, carries) = addReals2 xs ys
    in (z :> zs, carry :> carries)

addReals3 :: R HalfTrit (Half b) -> R HalfTrit (Half b) -> R Trit (Half b)
addReals3 (x :> xs) (y :> ys) = 
    let (_, z) = adder3 x y
        zs = addReals3 xs ys
    in z :> zs

-- There ought to be a way to get addReals to only add one bit at the
-- top, but I haven't found it yet.
addReals :: R Trit (Half (Half b)) -> R Trit (Half (Half b)) -> R Trit b
addReals xs ys = 
    let (z1 :> zs1, carry1) = addReals1 xs ys
        (z2 :> zs2, carry2) = addReals2 zs1 carry1
        (z, z') = adder2 z1 z2
    in promote z :> promote z' :> addReals3 zs2 carry2

viewTrits :: R Trit b -> String
viewTrits (x :> xs) = show x ++ viewTrits xs

interpN :: Int -> R Trit b -> Rational
interpN 0 _ = 0
interpN n (x :> xs) = interp x + interpN (n-1) xs / 2

fromRat :: Rational -> R Trit b
fromRat r 
    | r < 0 || r >= 2 = error "fromRational: out of range"
    | r < 1/2 = TA :> fromRat (2*r)
    | r < 1   = TB :> fromRat (2*(r - 1/2))
    | otherwise = TC :> fromRat (2*(r - 1))
