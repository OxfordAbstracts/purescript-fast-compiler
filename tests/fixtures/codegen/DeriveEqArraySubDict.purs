module DeriveEqArraySubDict where

-- Regression: derive Eq for constructors with parameterized type fields
-- generated eq(eqArray) instead of eq(eqArray(eqString)), causing
-- "eqArray is not a function" at runtime.

import Prelude

data Wrapper
  = Single String
  | Multi (Array String)

derive instance eqWrapper :: Eq Wrapper

test :: Boolean
test =
  Multi ["a", "b"] == Multi ["a", "b"]
    && Multi ["a"] /= Multi ["b"]
    && Single "x" == Single "x"

-- TEST: true
