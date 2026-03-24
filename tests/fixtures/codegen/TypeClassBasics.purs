module TypeClassBasics where

-- Basic class with one method
class MyEq a where
  myEq :: a -> a -> Boolean

-- Instance for Int
instance myEqInt :: MyEq Int where
  myEq _ _ = true

-- Instance for String
instance myEqString :: MyEq String where
  myEq _ _ = true

-- Using the class method with a constraint
isEqual :: forall a. MyEq a => a -> a -> Boolean
isEqual x y = myEq x y

-- Class with two methods
class MyOrd a where
  myCompare :: a -> a -> Int
  myLte :: a -> a -> Boolean

instance myOrdInt :: MyOrd Int where
  myCompare _ _ = 0
  myLte _ _ = true

compareValues :: forall a. MyOrd a => a -> a -> Int
compareValues x y = myCompare x y

test = isEqual 1 1

-- TEST: true
