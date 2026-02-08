module N3
  ( Format(..)
  , parse
  , write
  )
  where

import Prelude

import Control.Promise (Promise, toAffE)
import Effect (Effect)
import Effect.Aff (Aff)
import RDF (Quad)

data Format = Turtle | TriG | NTriples | NQuads

foreign import parseImpl :: String -> Format -> String -> Effect (Promise (Array Quad))

-- | Given a base URI and an RDF serialization format, parses a given string.
parse :: String -> Format -> String -> Aff (Array Quad)
parse base format = (parseImpl base format) >>> toAffE

foreign import writeImpl :: String -> Format -> Array Quad -> Effect (Promise String)

-- | Given a base URI and an RDF serialization format, serializes an array of quads.
write :: String -> Format -> Array Quad -> Aff String
write base format = (writeImpl base format) >>> toAffE
