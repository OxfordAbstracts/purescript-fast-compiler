module TestBuilder where

import Prelude
import Builder (Builder(..), build)

-- Just test that the module loads without ReferenceError.
-- When Builder/index.js initializes, it runs:
--   var semigroupoidBuilder = semigroupoidFunction;  (BUG: undefined)
-- This should be: var semigroupoidBuilder = {};
-- If it fails, we get ReferenceError at module load time.

addOne :: Builder Int Int
addOne = Builder (_ + 1)

-- TEST: "4"
test :: String
test = show (build addOne 3)
