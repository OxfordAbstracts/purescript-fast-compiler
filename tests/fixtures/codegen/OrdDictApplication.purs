module OrdDictApplication where

-- Tests that class dictionaries are properly applied when calling
-- a polymorphic function with a class constraint at a concrete type.
-- Bug: generated JS emits `smaller(1)(2)` instead of `smaller(myOrdInt)(1)(2)`.

class MyOrd a where
  myCompare :: a -> a -> String

instance myOrdInt :: MyOrd Int where
  myCompare _ _ = "compared"

-- Polymorphic: should accept a dict parameter in generated JS
smaller :: forall a. MyOrd a => a -> a -> String
smaller x y = myCompare x y

-- Concrete call site: must pass the MyOrd Int dict
test :: String
test = smaller 1 2
