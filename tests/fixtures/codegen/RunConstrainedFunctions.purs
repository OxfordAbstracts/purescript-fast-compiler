-- | Node.js-executable tests for typeclass dictionary dispatch.
module RunConstrainedFunctions where

class Describable a where
  describe :: a -> String

instance describableBool :: Describable Boolean where
  describe true = "true"
  describe false = "false"

instance describableInt :: Describable Int where
  describe _ = "int"

showDesc :: forall a. Describable a => a -> String
showDesc x = describe x
