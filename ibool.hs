import Prelude hiding (not)
import qualified Prelude

class BooleanAlgebra a where
    not :: a -> a
    (\/) :: a -> a -> a
    (/\) :: a -> a -> a

instance BooleanAlgebra Bool where
    not = Prelude.not
    (\/) = (||)
    (/\) = (&&)

data IBool = Bool :+ Bool


(a :+ b) \/ (c :+ d) = 
