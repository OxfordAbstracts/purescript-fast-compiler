-- | Take the Fast Fourier Transform of a real valued array, returning
-- | a complex valued array using the Cartesian package. Note, this is
-- | much slower than the functions provided by the FFT module. Note
-- | that this module doesn't expose any conversions between RealArray
-- | and Array Number. It is more efficient to unwrap the RealArray
-- | newtype constructor.
module FFT.Real (transform) where

import Prelude

import Data.Complex (Cartesian)
import FFT (FFT, RealArray(..), realTransform)
import FFT.Complex (fromComplexArray)

-- | Compute the Fast Fourier Transform of an array of real numbers.
transform :: FFT -> Array Number -> Array (Cartesian Number)
transform fft =
  fromComplexArray <<< realTransform fft <<< RealArray
