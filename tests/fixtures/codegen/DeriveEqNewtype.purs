module DeriveEqNewtype where

import Prelude

-- Derive Eq for a newtype (not derive newtype instance).
-- The generated eq should compare the underlying Int values.
newtype Seed = Seed Int

derive instance eqSeed :: Eq Seed

test = Seed 1 == Seed 1

-- TEST: true
