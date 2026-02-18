-- | Tests for instances that themselves have constraints,
-- | e.g. `instance (MyShow a) => MyShow (Maybe a) where ...`
-- | The instance value becomes a function taking the constraint dict.
module InstanceConstraints where

data Maybe a = Nothing | Just a

class MyShow a where
  myShow :: a -> String

instance myShowInt :: MyShow Int where
  myShow _ = "int"

-- This instance requires MyShow a, so it becomes:
-- var myShowMaybe = function(dictMyShow) { return { myShow: ... }; }
instance myShowMaybe :: MyShow a => MyShow (Maybe a) where
  myShow Nothing = "nothing"
  myShow (Just x) = myShow x

showMaybeValue :: forall a. MyShow a => Maybe a -> String
showMaybeValue x = myShow x
