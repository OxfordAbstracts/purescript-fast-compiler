module ClassMethodDict where

class MyEq a where
  myEq :: a -> a -> Boolean

instance myEqInt :: MyEq Int where
  myEq _ _ = true

-- Constrained function that threads dict to class method
checkEq :: forall a. MyEq a => a -> a -> Boolean
checkEq x y = myEq x y

test = checkEq 3 3

-- TEST: true
