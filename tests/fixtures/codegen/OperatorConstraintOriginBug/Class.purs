-- | Class module that also wildcard-imports Decoders.
-- | This is the key bug trigger: because Class does "import Decoders"
-- | (wildcard), Decoders's value_origins propagate into Class's value_origins.
-- | Then when a facade imports Class before Combinators, Class's polluted origins
-- | beat Combinators's correct origins.
-- |
-- | Mirrors Data.Argonaut.Decode.Class which does:
-- |   import Data.Argonaut.Decode.Decoders   (wildcard)
module Class where

import Decoders

-- | The typeclass whose method acts as the decoder function.
-- | decode :: Int -> a  (mirrors decodeJson :: Json -> Either err a)
class Decode a where
  decode :: Int -> a

-- | Concrete instance: decode identity for Int.
instance decodeInt :: Decode Int where
  decode n = n
