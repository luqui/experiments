{-# LANGUAGE PolyKinds, RankNTypes, TypeOperators, TypeFamilies, UndecidableInstances, ScopedTypeVariables #-}

import Prelude hiding (id, (.), fst, snd, curry, uncurry)
import GHC.Prim (Any)
import Unsafe.Coerce (unsafeCoerce)



-- The combinators allow us to define data types of arbitrary kind,
-- within the (. -> *) -> * monad at the type level.
newtype Return (k :: k) (c :: k -> *) = Return { getReturn :: c k }

newtype Id (x :: *) = Id { getId :: x }

newtype ((f :: a -> b) <$> (x :: (a -> *) -> *)) (c :: y -> *) 
    = FMap { getFMap :: x (c :. f) }

newtype Join (x :: (((a -> *) -> *) -> *) -> *) (c :: a -> *)
    = Join { getJoin :: x (ApplyTo c) }

newtype ((fc :: ((a -> b) -> *) -> *) <*> (xc :: (a -> *) -> *)) (c :: b -> *)
    = Ap { getAp :: fc (xc :. ((:.) c)) }

newtype (f :. g) x = Compose { getCompose :: f (g x) }

newtype ApplyTo (x :: a) (f :: (a -> *)) = ApplyTo { getApplyTo :: f x }

newtype Hask (a :: (* -> *) -> *) (b :: (* -> *) -> *)
    = Hask { getHask :: a Id -> b Id }

-- Lift is a functor from hom to Lift hom
newtype Lift hom a b = Lift { getLift :: hom (Return a) (Return b) }

-- Unlift is a functor from Lift hom to hom
newtype Unlift hom (a :: (a -> *) -> *) (b :: (b -> *) -> *)
    = Unlift { getUnlift :: (hom <$> a <*> b) Id }

returnIso = Iso getReturn Return
idIso = Iso getId Id
fmapIso = Iso getFMap FMap
joinIso = Iso getJoin Join
apIso = Iso getAp Ap
composeIso = Iso getCompose Compose
applyToIso = Iso getApplyTo ApplyTo
haskIso = Iso getHask Hask
liftIso = Iso getLift Lift
unliftIso = Iso getUnlift Unlift


{-
class Category (hom :: ((k -> *) -> *) -> ((k -> *) -> *) -> *) where
    id :: hom a a
    (.) :: hom b c -> hom a b -> hom a c
-}

class Category hom where
    id :: hom a a
    (.) :: hom b c -> hom a b -> hom a c

data Iso a b = Iso { forward :: a -> b, backward :: b -> a }

instance Category Iso where
    id = Iso id id
    Iso g g' . Iso f f' = Iso (g . f) (f' . g')

instance Category (->) where
    id x = x
    (g . f) x = g (f x)


(.>) :: (Category hom) => hom a b -> hom b c -> hom a c
(.>) = flip (.)


-- they are inverses
liftUnlift :: Iso (Lift (Unlift hom) a b) (hom a b)
liftUnlift =      -- :: Lift (Unlift hom) a b
       liftIso    -- :: Unlift hom (Return a) (Return b)
    .> unliftIso  -- :: (hom <$> Return a <*> Return b) Id
    .> apIso      -- :: (hom <$> Return a) (Return b :. ((:.) Id))
    .> fmapIso    -- :: Return a ((Return b :. ((:.) Id)) :. hom)
    .> returnIso  -- :: ((Return b :. ((:.) Id)) :. hom) a
    .> composeIso -- :: (Return b :. ((:.) Id)) (hom a)
    .> composeIso -- :: Return b (Id :. hom a)
    .> returnIso  -- :: (Id :. hom a) b
    .> composeIso -- :: Id (hom a b)
    .> idIso      -- :: hom a b

{-
-- ran into trouble here.. need some constraint on a.
unliftLift :: Iso (Unlift (Lift hom) a b) (hom a b)
unliftLift =      -- :: Unlift (Lift hom) a b
       unliftIso  -- :: (Lift hom <$> a <*> b) Id
    .> apIso      -- :: (Lift hom <$> a) (b :. ((:.) Id))
    .> fmapIso    -- :: a ((b :. ((:.) Id)) :. Lift hom)
    ...?
-}


instance Category Hask where
    id = Hask (\x -> x)
    Hask g . Hask f = Hask (\x -> g (f x))

instance Category hom => Category (Lift hom) where
    id = Lift id
    Lift g . Lift f = Lift (g . f)

newtype PreNT (hom :: ((c -> *) -> *) -> ((c -> *) -> *) -> *)
           (f :: b -> c)
           (g :: b -> c)
    = PreNT { getPreNT :: forall (x :: b). Lift hom (f x) (g x) }

type NT hom = PreNT (Unlift hom)

getNT :: NT hom f g -> hom (f a) (g a)
getNT =                    -- :: NT (Unlift hom) f g
       getPreNT            -- :: Lift (Unlift hom) (f x) (g x)
    .> forward liftUnlift  -- :: hom (f a) (g a)

instance (Category hom) => Category (PreNT hom) where
    id = PreNT id
    PreNT g . PreNT f = PreNT (g . f)

{-
newtype NT hom f g = NT (forall x. hom (f x) (g x))


class Category hom => Products (hom :: k -> k -> *) where
    type Product hom :: k -> k -> k
    (&&&) :: hom a b -> hom a c -> hom a (Product hom b c)
    fst :: hom (Product hom a b) a
    snd :: hom (Product hom a b) b

class Products hom => Arrows (hom :: k -> k -> *) where
    type Arrow hom :: k -> k -> k
    curry :: hom (Product hom a b) c -> hom a (Arrow hom b c)
    uncurry :: hom a (Arrow hom b c) -> hom (Product hom a b) c

class (Category hom) => ConstantFunctors (hom :: k -> k -> *) where
    type Const hom :: j -> k
-}

