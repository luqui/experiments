-- lambda calculus to composition notation in CCCs

type Name = String

data Term 
    = Free Name
    | Var Int
    | Lambda Term
    | App Term Term
    deriving Show

data CCMor
    = CName Name
    | Id
    | Then CCMor CCMor
    | Curry CCMor          -- [ a*b -> c ]      -> [ a -> (b -> c) ]
    | Uncurry CCMor        -- [ a -> (b -> c) ] -> [ a*b -> c ]
    | Unit                 -- a -> 1
    | Proj1                -- a * b -> a
    | Proj2                -- a * b -> b
    | Bracket CCMor CCMor  -- [ a -> b ] -> [ a -> c ] -> [ a -> b*c ]
    deriving Show


convert :: Term -> CCMor
convert (Free n)   = CName n
convert (Var i)    = foldr Then Proj2 (replicate i Proj1) 
convert (Lambda t) = Curry (convert t)    -- (X * a -> b) -> (X -> (a -> b))
convert (App x y)  = Then (Bracket (convert x) (convert y)) (Uncurry Id)

then' = flip (.)
bracket f g x = (f x, g x)
