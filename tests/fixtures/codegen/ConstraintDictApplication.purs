module ConstraintDictApplication where

import Prelude

-- Minimal repro: a function with a constraint that gets partially applied.
-- The constraint dict should be passed before the value arguments.

class MyClass a where
  myMethod :: a -> String

instance myClassInt :: MyClass Int where
  myMethod _ = "int"

-- A function with a constraint
constrained :: forall a. MyClass a => a -> String
constrained x = myMethod x

-- Point-free partial application (should pass dict, then value)
test = constrained 42

-- TEST: "int"
