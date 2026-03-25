module DeriveOrdNewtype where

import Prelude

-- Derive Ord for a newtype (not derive newtype instance).
-- The generated compare should delegate to the underlying Int's ordInt.
newtype Seed = Seed Int

derive instance eqSeed :: Eq Seed
derive instance ordSeed :: Ord Seed

test = Seed 1 < Seed 2

-- TEST: true
