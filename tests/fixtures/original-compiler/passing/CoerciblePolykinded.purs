module Main where

import Safe.Coerce (coerce)
import Prim.Coerce (class Coercible)

-- Regression test: Coercible should be polykinded (forall k. k -> k -> Constraint),
-- not just (Type -> Type -> Constraint). This allows coercing between newtypes
-- used at higher kinds.

newtype MyFunctor f a = MyFunctor (f a)

myCoerce :: forall a b. Coercible a b => a -> b
myCoerce = coerce

-- Coercing a value at Type kind
newtype Name = Name String

getName :: Name -> String
getName = myCoerce
