module TestConstrainedWhereOp where

import Prelude

-- Minimal reproduction: constrained function with where clause that uses
-- an operator from the constraint in a point-free value binding.
-- Bug: codegen generates __constraint_1 instead of dictOrd.
-- Pattern from Data.Map.Internal.insert.

myCompare :: forall a. Ord a => a -> a -> String
myCompare x = go
  where
  go = case _ of
    y -> case compare x y of
      EQ -> "equal"
      LT -> "less"
      GT -> "greater"

-- TEST: "equal"
test = myCompare 1 1
