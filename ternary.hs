import Control.Arrow

class (Eq a) => Bit a where
    zero :: a
    halfAdder :: a -> a -> (a,a)

data B2 = B0 | B1
    deriving (Eq,Ord,Show)

instance Bit B2 where
    zero = B0
    halfAdder B0 B0 = (B0,B0)
    halfAdder B0 B1 = (B1,B0)
    halfAdder B1 B0 = (B1,B0)
    halfAdder B1 B1 = (B0,B1)

data T2 = T0 | THalf | T1
    deriving (Eq,Ord,Show)

instance Bit T2 where
    zero = T0
    {-
    halfAdder T0    T0    = (T0,T0)
    halfAdder T0    THalf = (THalf,T0)
    halfAdder T0    T1    = (T1,T0)
    halfAdder THalf T0    = (THalf,T0)
    halfAdder THalf THalf = (T1,T0)
    halfAdder THalf T1    = (THalf,THalf)
    halfAdder T1    T0    = (T1,T0)
    halfAdder T1    THalf = (THalf,THalf)
    halfAdder T1    T1    = (T1,THalf)  -- key line
    -- T1 is never carried
    -}

    halfAdder T0    T0    = (T0,T0)
    halfAdder T0    THalf = (THalf,T0)
    halfAdder T0    T1    = (T0,THalf)
    halfAdder THalf T0    = (THalf,T0)
    halfAdder THalf THalf = (T0,THalf)
    halfAdder THalf T1    = (THalf,THalf)
    halfAdder T1    T0    = (T0,THalf)
    halfAdder T1    THalf = (THalf,THalf)
    halfAdder T1    T1    = (T0,T1)
    -- T1 is never output
    
split :: T2 -> (T2,T2)
split T0 = (T0,T0)
split THalf = (THalf,T0)
split T1 = (THalf,THalf)

-- The digit can depend on x, y, and cIn
-- and cOut can depend on x and y
adderT :: T2 -> T2 -> T2 -> (T2,T2)
adderT x y cIn = (xyc,c')
    where
    (xy,c') = halfAdder x y
    -- xy <= 1/2
    (xyc,c'') = halfAdder xy cIn
    cOut | (k, z) <- halfAdder c' c''
         , z == zero  
         = k

addT :: [T2] -> [T2] -> ([T2],T2)
addT (x:xs) (y:ys) = (xy:xsys, c')
    where
    (xsys,c) = addT xs ys
    (xy,c') = adderT x y c



