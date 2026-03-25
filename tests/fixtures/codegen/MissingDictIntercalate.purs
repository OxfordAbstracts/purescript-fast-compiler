module MissingDictIntercalate where

import Prelude

-- Pattern: partial application of a constrained function at a concrete type.
-- The constraint dict must be inserted before the value argument.

-- mempty uses Monoid constraint. When used at String type,
-- the monoidString dict should be inserted.
test :: String
test = mempty <> "world"

-- TEST: "world"
