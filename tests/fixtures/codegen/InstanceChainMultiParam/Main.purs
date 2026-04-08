module Main where

-- Tests that instance chain resolution picks the correct instance
-- (combineBoxBox) when both args are Box, not combineStringBox.

import Prelude
import Lib (class Combine, combine, Box(..), Pair(..))

-- This should resolve to combineBoxBox, producing Pair 1 2.
-- Bug: registry (Combine, Box) mapped to combineStringBox (registered first),
-- so the fallback returned Var(combineStringBox) instead of Var(combineBoxBox).
test :: Pair Int Int
test = combine (Box 1) (Box 2)

-- TEST: {"value0":1,"value1":2}
