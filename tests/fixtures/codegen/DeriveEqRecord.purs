module DeriveEqRecord where

-- Regression: derive Eq for sum types with record fields generated
-- x.value0 === y.value0 (object identity, always false) instead of
-- field-by-field comparison (x.value0.id === y.value0.id && ...).

import Prelude

data Route
  = Home
  | Profile { name :: String, age :: Int }
  | Settings String

derive instance eqRoute :: Eq Route

test :: Boolean
test =
  Profile { name: "Alice", age: 30 } == Profile { name: "Alice", age: 30 }
    && Profile { name: "A", age: 1 } /= Profile { name: "B", age: 1 }
    && Home == Home
    && Settings "x" == Settings "x"
    && Home /= Settings "y"

-- TEST: true
