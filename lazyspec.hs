{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Applicative
import Control.Monad (join)

data Prim
    = PrimInt Integer
    | PrimSucc

instance Show Prim where
    show (PrimInt x) = show x

type Depth = Int

data Value
    = VPrim Prim
    | VVar Depth
    | VFun (Value -> Value)
    | VApp Value Value


instance Show Value where
    show (VPrim p) = show p
    show (VVar d)  = "var" ++ show d
    show (VFun _)  = "<fun>"
    show (VApp v w) = "(" ++ show v ++ " " ++ show w ++ ")"


newtype Run a = Run { run :: Depth -> a }
    deriving (Functor, Applicative, Monad)

depth :: Run Depth
depth = Run id

scope :: Run a -> Run a
scope f = Run (\d -> run f (d+1))


infixl 9 %
(%) :: Run Value -> Run Value -> Run Value
f % x = liftA2 app f x

app :: Value -> Value -> Value
VFun f `app` x = f x
VVar d `app` x = VVar d `VApp` x
VApp x y `app` z = VApp x y `VApp` z
VPrim PrimSucc `app` VPrim (PrimInt z) = VPrim . PrimInt $! z+1
VPrim PrimSucc `app` VApp x y = VPrim PrimSucc `VApp` (x `VApp` y)
VPrim PrimSucc `app` VVar d = VPrim PrimSucc `VApp` VVar d
_ `app` _ = error "Malformed apply"

lambda :: (Value -> Run Value) -> Run Value
lambda f = do
    (d,body) <- scope $ do
        d <- depth
        body <- f (VVar d)
        return (d,body)
    return $ VFun (subst d body)

fun :: (Run Value -> Run Value) -> Run Value
fun f = lambda (f . return)

subst :: Depth -> Value -> Value -> Value
subst d (VPrim p) val = VPrim p
subst d (VVar d') val
    = case compare d d' of
        LT -> VVar $! d'-1
        EQ -> val
        GT -> VVar d'
subst d (VFun f) val = VFun (\x -> d `seq` subst (d+1) (f x) val')
    where
    val' = inc d val
subst d (VApp f@(VFun {}) x) val = subst d (f `app` x) val
subst d (VApp f x) val = subst d f val `app` subst d x val

inc :: Depth -> Value -> Value
inc d (VPrim p) = VPrim p
inc d (VVar d')
    = case compare d d' of
        LT -> VVar $! d'+1
        EQ -> VVar d'
        GT -> VVar d'
inc d (VFun f) = VFun (inc (d+1).f)

int :: Integer -> Run Value
int = return . VPrim . PrimInt

suc :: Run Value
suc = return (VPrim PrimSucc)
