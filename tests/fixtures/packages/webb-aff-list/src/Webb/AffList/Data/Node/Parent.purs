module Webb.AffList.Data.Node.Parent where

import Prelude

import Data.Newtype (class Newtype)
import Effect.Aff (Aff)
import Unsafe.Coerce (unsafeCoerce)



class Parent a where
  cancel :: a -> Aff Unit

newtype Parent_ = Parent__ (forall r. (forall z. Parent z => z -> r) -> r)

-- Way to recover the original type unsafely.
unsafeRecover :: forall a. Parent_ -> a
unsafeRecover (Parent__ f) = f (\z -> unsafeCoerce z :: a)

instance Show Parent_ where show _ = "Parent"

wrap :: forall z. Parent z => z -> Parent_
wrap z = Parent__ (_ $ z)

instance Parent (Parent_) where 
  cancel (Parent__ run) = run cancel
