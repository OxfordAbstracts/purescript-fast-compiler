module Main where

import Lib as R
import Types (ResponseUpdate)

-- Import a zero-param alias that expands to a qualified data type
-- with the same unqualified name (R.ResponseUpdate).
-- The alias should expand correctly without infinite loops,
-- and the expanded type should unify with the data constructors.
test :: ResponseUpdate
test = R.ResponseUpdate 42 true
