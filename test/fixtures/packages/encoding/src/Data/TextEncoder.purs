module Data.TextEncoder
  ( encode
  , encodeUtf8
  )
where

import Data.ArrayBuffer.Types  ( Uint8Array )
import Data.Function.Uncurried ( Fn1, runFn1 )


-- | Encodes a `String` to a `Uint8Array` using UTF-8 encoding.
encode :: String -> Uint8Array
encode str = runFn1 encodeImpl str

foreign import encodeImpl :: Fn1 String Uint8Array

-- | Encodes a `String` to a `Uint8Array` using UTF-8 encoding.
-- | This is an alias for `encode` that is provided for symmetry with
-- | `decodeUtf8`.
encodeUtf8 :: String -> Uint8Array
encodeUtf8 = encode
