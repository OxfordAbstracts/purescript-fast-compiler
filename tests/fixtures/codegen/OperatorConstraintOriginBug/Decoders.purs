-- | Raw (unconstrained) decoder function.
-- | Mirrors Data.Argonaut.Decode.Decoders.getFieldOptional:
-- |   takes a decoder function directly (not a typeclass dict).
module Decoders where

-- | Apply a decoder function to an input.
-- | (Int -> a) = decoder function; Int = "object"; Int = "key"
getField :: forall a. (Int -> a) -> Int -> Int -> a
getField decoder obj _key = decoder obj
