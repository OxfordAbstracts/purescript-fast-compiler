module ClassMethodDict where

class MyOrd a where
  myCompare :: a -> a -> Int

instance myOrdInt :: MyOrd Int where
  myCompare _ _ = 0

-- This function uses a class method through a constraint.
-- The codegen must generate: function(dictMyOrd) { return function(k) { return function(mk) { return myCompare(dictMyOrd)(k)(mk); }; }; }
-- Without dictionary passing, it generates: function(k) { return function(mk) { return myCompare(k)(mk); }; }
-- which fails at runtime because myCompare is not a function (it's an accessor).
lookup :: forall a. MyOrd a => a -> a -> Int
lookup k mk = myCompare k mk
