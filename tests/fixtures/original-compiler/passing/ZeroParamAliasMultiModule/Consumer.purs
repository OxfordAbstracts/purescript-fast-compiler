module Consumer where

import Data as D
import Types (A)

-- A second module importing the same zero-param alias.
-- This must also expand correctly — the fix must not
-- mark the alias as self-referential globally.
consume :: A -> Int
consume (D.A n _) = n
consume D.B = 0
