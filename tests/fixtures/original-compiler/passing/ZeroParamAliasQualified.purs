module Main where

import Lib as R
import Types (T)

-- Import a zero-param alias that expands to a qualified data type
-- with the same unqualified name (R.T).
-- The alias should expand correctly without infinite loops,
-- and the expanded type should unify with the data constructors.
test :: T
test = R.T 42 true
