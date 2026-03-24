-- Defines the Bind class (like Control.Bind).
module MyBind where

import Prelude

class MyBind (m :: Type -> Type) where
  myBind :: forall a b. m a -> (a -> m b) -> m b
