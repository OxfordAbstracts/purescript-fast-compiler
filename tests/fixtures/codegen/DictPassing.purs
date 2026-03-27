module DictPassing where

-- Test dictionary-passing for constrained functions and class methods.
-- This models the pattern that causes "Failed pattern match" in Data.Maybe
-- when dict params are missing: the caller's dict arg shifts all other args,
-- causing pattern matches on the wrong values.

class MyFunctor f where
  myMap :: forall a b. (a -> b) -> f a -> f b

data MyMaybe a = MyNothing | MyJust a

instance myFunctorMyMaybe :: MyFunctor MyMaybe where
  myMap fn (MyJust x) = MyJust (fn x)
  myMap _  _          = MyNothing

-- Constrained function: must take a dict param and thread it to myMap
liftF :: forall f a b. MyFunctor f => (a -> b) -> f a -> f b
liftF f x = myMap f x
