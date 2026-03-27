-- | Constrained wrapper around Decoders using the Class typeclass.
-- | Mirrors Data.Argonaut.Decode.Combinators:
-- |   getFieldOptional = Decoders.getFieldOptional decodeJson
-- |   infix 7 getFieldOptional as .:!
module Combinators where

import Class (class Decode, decode)
import Decoders as D

-- | Constrained getField: point-free definition that applies the class method.
-- | D.getField :: (Int -> a) -> Int -> Int -> a
-- | decode     :: Decode a => Int -> a
-- | So: getField :: forall a. Decode a => Int -> Int -> a
-- |   = D.getField decode
-- | Should codegen: var getField = function(dictDecode) { return D.getField(Class.decode(dictDecode)); }
getField :: forall a. Decode a => Int -> Int -> a
getField = D.getField decode

infix 7 getField as .!

