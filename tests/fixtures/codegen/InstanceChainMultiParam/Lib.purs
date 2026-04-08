module Lib where

-- Minimal reproduction of instance chain dict resolution bug.
-- When multiple instances share a head type constructor in different
-- positions, the registry (indexed by head) could pick the wrong instance.
-- E.g., GSep String (Box a) b vs GSep (Box a) (Box b) (Pair a b).

import Prelude

data Box a = Box a
data Pair a b = Pair a b

class Combine a b c | a b -> c where
  combine :: a -> b -> c

-- Instance chain: String+String, String+Box, Box+Box
instance combineStringString :: Combine String String String where
  combine a b = a <> b
else instance combineStringBox :: Combine String (Box a) (Box a) where
  combine _ b = b
else instance combineBoxBox :: Combine (Box a) (Box b) (Pair a b) where
  combine (Box a) (Box b) = Pair a b
