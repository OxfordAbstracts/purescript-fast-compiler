-- | Tests for typeclass dictionary passing in generated JavaScript.
-- | Constrained functions must receive a dictionary argument for each constraint,
-- | and class method calls inside must be dispatched through the dict.
module ConstrainedFunctions where

class Describable a where
  describe :: a -> String

class MyEq a where
  myEq :: a -> a -> Boolean

instance describableBool :: Describable Boolean where
  describe true = "true"
  describe false = "false"

instance describableInt :: Describable Int where
  describe _ = "int"

instance myEqInt :: MyEq Int where
  myEq _ _ = true

-- Simple single-constraint function
showDesc :: forall a. Describable a => a -> String
showDesc x = describe x

-- Multiple constraints: both dicts are threaded as separate parameters
describeTwo :: forall a. Describable a => MyEq a => a -> a -> String
describeTwo x _ = describe x
