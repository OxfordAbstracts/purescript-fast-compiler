module OverlapLocalTypeShadow.Dep where

class MyTrans (t :: (Type -> Type) -> Type -> Type) where
  lift :: forall m a. m a -> t m a
