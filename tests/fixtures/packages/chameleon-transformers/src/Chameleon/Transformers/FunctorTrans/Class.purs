module Chameleon.Transformers.FunctorTrans.Class where

import Prelude

class
  FunctorTrans (t :: (Type -> Type) -> Type -> Type)
  where
  lift :: forall f a. Functor f => f a -> t f a