module MyEq where

class MyEq a where
  myEq :: a -> a -> Boolean

instance myEqInt :: MyEq Int where
  myEq _ _ = true

myLookup :: forall a. MyEq a => a -> Boolean
myLookup _ = true
