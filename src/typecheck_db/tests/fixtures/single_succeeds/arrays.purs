module Test.Arrays where

-- Literal array — element types unify.
ints :: Array Int
ints = [1, 2, 3]

-- Empty array is polymorphic.
empty :: forall a. Array a
empty = []

-- Pattern-binding on an array.
firstTwoSame :: Array Int -> Int
firstTwoSame xs = case xs of
  [a, _] -> a
  _ -> 0
