module MyOrd where

import MyEq

class MyEq a <= MyOrd a where
  myCompare :: a -> a -> Int

instance myOrdInt :: MyOrd Int where
  myCompare _ _ = 0

-- Function that takes MyOrd constraint but calls a function needing MyOrd
myUnion :: forall a. MyOrd a => a -> a -> Int
myUnion a b = myCompare a b

-- Function that takes MyOrd constraint but calls a function needing MyEq (superclass)
mySuperLookup :: forall a. MyOrd a => a -> Boolean
mySuperLookup = myLookup

-- Point-free that should pass MyOrd dict directly
outerFn :: forall a. MyOrd a => a -> a -> Int
outerFn = myUnion
