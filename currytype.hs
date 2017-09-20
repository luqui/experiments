{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

import Data.Kind (Type)


data Params = P Type Type

type family Identifier t where
    Identifier ('P i l) = i
type family Literal t where
    Literal ('P i l) = l

data Ast t
    = Ident (Identifier t)
    | Lit (Literal t)
    | Apply (Ast t) (Ast t)

deriving instance (Show (Identifier p), Show (Literal p)) => Show (Ast p)

test :: Ast (P Int String)
test = Apply (Ident 42) (Lit "hello")
