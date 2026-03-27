-- | Facade module that re-exports Class and Combinators.
-- | The import ORDER is the critical trigger:
-- |   1. import Class  -- Class has value_origins[getField] = Decoders (via wildcard import)
-- |   2. import Combinators  -- or_insert won't override; getField stays → Decoders
-- |
-- | So Facade.value_origins[getField] = Decoders (wrong), not Combinators (correct).
-- | When Test.Main imports from Facade and uses .!, codegen traces .! → Decoders.getField
-- | and calls it without the dict.
-- |
-- | Mirrors Data.Argonaut.Decode:
-- |   import Data.Argonaut.Decode.Class (class DecodeJson, decodeJson)     -- first
-- |   import Data.Argonaut.Decode.Combinators (getField, ..., (.:!), ...)  -- second
module Facade
  ( module Class
  , module Combinators
  ) where

import Class (class Decode, decode)
import Combinators (getField, (.!))
