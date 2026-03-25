module TestSuperclassPassthrough where

import Prelude

-- Minimal reproduction: passing a constraint dict through to another function
-- that takes the same constraint. The codegen should pass dictOrd directly,
-- not apply a superclass accessor like dictOrd.Eq0().

myCompare :: forall a. Ord a => a -> a -> Ordering
myCompare a b = compare a b

myMax :: forall a. Ord a => a -> a -> a
myMax a b = case myCompare a b of
  GT -> a
  _ -> b

-- TEST: 5
test = myMax 3 5
