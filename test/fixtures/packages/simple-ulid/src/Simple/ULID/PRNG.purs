module Simple.ULID.PRNG
  ( PRNG
  , toEffect
  ) where

import Effect (Effect)
import Unsafe.Coerce (unsafeCoerce)

foreign import data PRNG :: Type

toEffect :: PRNG -> Effect Number
toEffect = unsafeCoerce
