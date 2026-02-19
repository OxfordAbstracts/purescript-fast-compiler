module MyEq where

class MyEq a where
  myEq :: a -> a -> Boolean

instance myEqInt :: MyEq Int where
  myEq x y = true

instance myEqArray :: MyEq a => MyEq (Array a) where
  myEq xs ys = true
