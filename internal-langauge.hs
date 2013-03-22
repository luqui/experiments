{-# LANGUAGE PolyKinds, RankNTypes, TypeFamilies, ExistentialQuantification, TypeOperators, MultiParamTypeClasses, FlexibleInstances #-}

import Prelude hiding (id, (.), fst, snd, curry, uncurry)

import Unsafe.Coerce (unsafeCoerce)

class Category hom where
    id :: hom a a
    (.) :: hom b c -> hom a b -> hom a c

instance Category (->) where
    id x = x
    (g . f) x = g (f x)


class (Category hom) => Products (hom :: k -> k -> *) where
    type Product hom :: k -> k -> k
    (&&&) :: hom a b -> hom a c -> hom a (Product hom b c)
    fst :: hom (Product hom b c) b
    snd :: hom (Product hom b c) c

instance Products (->) where
    type Product (->) = (,)
    (f &&& g) x = (f x, g x)
    fst (x,_) = x
    snd (_,y) = y

class (Category hom) => TerminalObject (hom :: k -> k -> *) where
    type Terminal hom :: k
    terminal :: hom a (Terminal hom)

instance TerminalObject (->) where
    type Terminal (->) = ()
    terminal = const ()

class (Products hom, TerminalObject hom) 
    => CartesianClosed (hom :: k -> k -> *) where
    type Arrow hom :: k -> k -> k
    curry :: hom (Product hom a b) c -> hom a (Arrow hom b c)
    uncurry :: hom a (Arrow hom b c) -> hom (Product hom a b) c

instance CartesianClosed (->) where
    type Arrow (->) = (->)
    curry f x y = f (x,y)
    uncurry f (x,y) = f x y

type Hom hom b c = forall a. hom a b -> hom a c
type Obj hom a   = hom (Terminal hom) a

id' :: Hom hom a a
id' x = x

compose' :: Hom hom b c -> Hom hom a b -> Hom hom a c
compose' f g x = f (g x)

apply :: Hom hom a b -> Obj hom a -> Obj hom b
apply f x = f x

fun :: (CartesianClosed hom)
         => Obj hom (Arrow hom a b)
         -> Hom hom a b
fun tab za = uncurry tab . (terminal &&& za)

apply2 :: (CartesianClosed hom) 
       => Hom hom a (Arrow hom b c) -> Obj hom a -> Obj hom b -> Obj hom c
apply2 f x y = fun (f x) y

andandand :: (Products hom) 
          =>  Hom hom a b -> Hom hom a c -> Hom hom a (Product hom b c)
andandand f g x = f x &&& g x
