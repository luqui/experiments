{-# LANGUAGE PolyKinds, DataKinds, KindSignatures, RankNTypes, GADTs, TypeFamilies #-}

import Control.Applicative

-- getZ :: Z f k -> f (k f)
-- Z :: f (k f) -> Z f k

data SynClass
    = SKind
    | SType
    | SExpr

data SynClassS s where
    SKindS :: SynClassS SKind
    STypeS :: SynClassS SType
    SExprS :: SynClassS SExpr

data family Syntax (t :: s) :: (s -> *) -> *

data instance Syntax SKind f
    = KStar

data instance Syntax SType f
    = f SType :-> f SType
    | TInt

data instance Syntax SExpr f
    = ELambda (f SType) (f SExpr)
    | EApp (f SExpr) (f SExpr)
    | EVar Int

data SynTree t where
    FixS :: SynClassS t -> Syntax t SynTree -> SynTree t

type Kind = Syntax SKind SynTree
type Type = Syntax SType SynTree
type Expr = Syntax SExpr SynTree

unroll :: SynTree t -> Syntax t SynTree
unroll (FixS _ sy) = sy

data TypeCheck t where
    TCKind :: TypeCheck SKind
    TCType :: Kind -> TypeCheck SType
    TCTerm :: Type -> TypeCheck SExpr

typeCheck :: [Type] -> SynTree t -> Maybe (TypeCheck t)
typeCheck _ (FixS SKindS KStar)     = Just TCKind

typeCheck env (FixS STypeS (t :-> u))
    | Just (TCType KStar) <- typeCheck env t
    , Just (TCType KStar) <- typeCheck env u = Just (TCType KStar)
    | otherwise                      = Nothing
typeCheck _ (FixS STypeS TInt) = Just (TCType KStar)

typeCheck env (FixS SExprS (EVar z)) = TCTerm <$> (env `at` z)
typeCheck env (FixS SExprS (EApp f x))
    | Just (TCTerm (dom :-> cod)) <- typeCheck env f
    , Just (TCTerm dom') <- typeCheck env x
    -- , dom == dom'
        = Just (TCTerm (unroll cod))
    | otherwise = Nothing
typeCheck env (FixS SExprS (ELambda t body))
    | Just (TCType KStar)    <- typeCheck env t
    , Just (TCTerm bodyType) <- typeCheck (unroll t:env) body = Just (TCTerm (unroll t ~> bodyType))
    | otherwise = Nothing

(~>) :: Syntax SType SynTree -> Syntax SType SynTree -> Syntax SType SynTree
t ~> u = FixS STypeS t :-> FixS STypeS u

at :: [a] -> Int -> Maybe a
at [] _ = Nothing
at (x:_) 0 = Just x
at (_:xs) n = at xs (n-1)
