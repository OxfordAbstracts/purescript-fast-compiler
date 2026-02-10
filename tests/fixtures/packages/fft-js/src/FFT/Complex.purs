-- | Take the Fast Fourier Transform of a complex valued array from,
-- | the Cartesian package, returning. Note, this is much slower than
-- | the functions provided by the FFT module.
module FFT.Complex (transform, toComplexArray, fromComplexArray) where

import Prelude

import Data.Array as Array
import Data.Array.ST as ArrayST
import Data.Complex (Cartesian(..), imag, real)
import Control.Monad.ST as ST
import Partial.Unsafe (unsafePartial)
import FFT (ComplexArray(..), FFT, newUnsafe)
import FFT as FFT

-- | Compute the Fast Fourier Transform of an array of complex numbers.
transform :: FFT -> Array (Cartesian Number) -> Array (Cartesian Number)
transform fft =
  fromComplexArray <<< FFT.transform fft <<< toComplexArray

-- * Conversions

-- | Convert an array of complex values numbers to a ComplexArray.
toComplexArray :: Array (Cartesian Number) -> ComplexArray
toComplexArray arr =
  ComplexArray $ Array.concatMap (\z -> [ real z, imag z ]) arr

-- | Convert ComplexArray to an array of complex values numbers.
fromComplexArray :: ComplexArray -> Array (Cartesian Number)
fromComplexArray (ComplexArray arr) =
  ArrayST.run do
    newArr <- newUnsafe (Array.length arr / 2)
    ST.for 0 (Array.length arr)
      ( \n -> ArrayST.modify n
          ( \_ -> Cartesian
              (unsafePartial $ Array.unsafeIndex arr (2 * n))
              (unsafePartial $ Array.unsafeIndex arr (2 * n + 1))
          )
          newArr
      )
    pure newArr
