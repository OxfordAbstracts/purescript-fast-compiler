module Test.InstanceContext where

-- Recursive instance context (Phase C fixed-point loop):
-- solving `Eq (Maybe Int)` needs `Eq Int` as a sub-constraint,
-- and the solver must discharge both.
data Maybe a = Nothing | Just a

class Eq a where
  eq :: a -> a -> Boolean

instance Eq Int where
  eq _ _ = true

instance Eq a => Eq (Maybe a) where
  eq Nothing Nothing = true
  eq (Just x) (Just y) = eq x y
  eq _ _ = false

-- Call site forces the outer + recursive resolution.
check :: Boolean
check = eq (Just 1) (Just 2)
