-- Provides concrete decoder implementations.
module MyDecoders where

data MyResult a = Ok a | Fail String

decodeString :: String -> MyResult String
decodeString s = Ok s

-- Mirrors Data.Argonaut.Decode.Decoders.decodeVoid
-- Returns MyResult Void-like (always fails).
decodeVoid :: forall a. String -> MyResult a
decodeVoid _ = Fail "cannot decode void"
