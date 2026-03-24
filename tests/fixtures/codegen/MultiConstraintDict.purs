-- Tests functions with multiple type class constraints.
-- Bug pattern: dict application order must match constraint declaration order.
-- When a function has multiple constraints, the codegen must apply dicts in order.
module MultiConstraintDict where

import Prelude

class MyClass a where
  myMethod :: a -> String

instance myClassInt :: MyClass Int where
  myMethod _ = "int"

-- Function with two constraints — both must be resolved correctly
useBoth :: forall a. Show a => MyClass a => a -> String
useBoth x = append (show x) (myMethod x)

test = useBoth 42

-- TEST: "42int"
