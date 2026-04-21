module MethodConstraintGiven.Lib where

class IxBind f where
  ibind :: forall a b. f a -> (a -> f b) -> f b

class IxMonad f where
  ipure :: forall a. a -> f a

class (IxBind f, IxMonad f) <= IxApply f where
  iapply :: forall a b. f (a -> b) -> f a -> f b
