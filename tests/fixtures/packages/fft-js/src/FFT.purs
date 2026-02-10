-- | Functions to compute the Fast Fourier Transform of an array.
-- |
-- | This module wraps the functionality of
-- | https://github.com/indutny/fft.js/ and makes it usable in
-- | PureScript, with a sprinkling of type safety.
-- |
-- | There are examples of how to use this module in the tests
-- | directory. Essentially, you need to make a new FFT object, then
-- | pass it to the required functions.
-- |
-- | fft.js provides different functions to take the Fourier Transform
-- | of both real and complex arrays. To separate these functions, we
-- | introduce the newtype wrappers ComplexArray and RealArray, to add
-- | semantic information to the type signature of the function.
-- |
-- | A complex valued array is simply an interwoven array of the real
-- | and imaginary parts. It looks like: [re0, im0, re1, im1, ...].
module FFT (FFT, ComplexArray(..), RealArray(..), class FFTArray, size, makeFFT, fftSize, fromComplexArray, createComplexArray, toComplexArray, transform, realTransform, inverseTransform, STComplexArray(..), STRealArray(..), fromComplexArrayST, toComplexArrayST, transformST, realTransformST, inverseTransformST, completeSpectrum, module FFT.Internal.Array) where

import Prelude (class Show, Unit, show, (/))
import Control.Monad.ST (ST)
import Data.Array as Array
import Data.Array.ST as ArrayST
import FFT.Internal.Array

-- | A class of arrays that you can take an FFT of. This class makes
-- | it easier to get the size of an array, which should match the
-- | fftSize of the FFT object used to compute a transform with.
class FFTArray a where
  size :: a -> Int

-- | Newtype wrapper for complex arrays. A complex array is equivalent
-- | to Array Number, where the values are of the form
-- | [re, im, re, im, ...].
newtype ComplexArray = ComplexArray (Array Number)

instance Show ComplexArray where
  show (ComplexArray arr) = show arr

instance FFTArray ComplexArray where
  size (ComplexArray arr) = Array.length arr / 2

-- | Newtype wrapper for real arrays.
newtype RealArray = RealArray (Array Number)

instance Show RealArray where
  show (RealArray arr) = show arr

instance FFTArray RealArray where
  size (RealArray arr) = Array.length arr

-- | A type representing the foreign FFT class.
foreign import data FFT :: Type

-- | Construct a new FFT object. The input is the length of the array
-- | that will have a Fourier Transform taking of. It must be a power
-- | of 2, and be greater than 1.
-- | The size is the number of numbers used in the array. For a real
-- | valued array, this is just the length. For a complex array, this
-- | is the length of the array / 2.
foreign import makeFFT :: Int -> FFT

-- | Get the size of the given FFT object.
foreign import fftSize :: FFT -> Int

-- | Create an array consisting of the real parts of the complex
-- | numbers provided in the given array.
foreign import fromComplexArray :: ComplexArray -> RealArray

-- | Create a zero filled complex array.
foreign import createComplexArray :: FFT -> ComplexArray

-- | Create a complex array from a given real array.
foreign import toComplexArray :: FFT -> RealArray -> ComplexArray

-- | Compute the Fast Fourier Transform of the given complex valued
-- | array.
foreign import transform :: FFT -> ComplexArray -> ComplexArray

-- | Compute the Fast Fourier Transform of the given real valued
-- | array. This is faster than creating a complex array from a real
-- | one and taking the Fourier Transformation.
foreign import realTransform :: FFT -> RealArray -> ComplexArray

-- | Compute the inverse Fourier transform of the given complex valued
-- | array.
foreign import inverseTransform :: FFT -> ComplexArray -> ComplexArray

-- | ST

-- | Newtype wrapper for complex arrays. A complex array is equivalent
-- | to STArray s Number, where the values are of the form
-- | [re, im, re, im, ...].
newtype STComplexArray s = STComplexArray (ArrayST.STArray s Number)

-- | Newtype wrapper for real arrays.
newtype STRealArray s = STRealArray (ArrayST.STArray s Number)

-- | Update an array with the real parts of the complex numbers
-- | provided in the given array.
foreign import fromComplexArrayST :: forall s. FFT -> ComplexArray -> STRealArray s -> ST s Unit

-- | Turn the given mutable array into a complex valued mutable array, formed from
-- | the real valued array provided. Note - the mutable array must
-- | have size double that of the real valued array.
foreign import toComplexArrayST :: forall s. FFT -> RealArray -> STComplexArray s -> ST s Unit

-- | Update the given mutable array with the Fourier transform of the
-- | given complex valued array.
foreign import transformST :: forall s. FFT -> ComplexArray -> STComplexArray s -> ST s Unit

-- | Update the given mutable array with the fourier transform of the
-- | given real valued array.
foreign import realTransformST :: forall s. FFT -> RealArray -> STRealArray s -> ST s Unit

-- | Update the given mutable array with the Inverse Fourier transform
-- | of the given complex valued array.
foreign import inverseTransformST :: forall s. FFT -> ComplexArray -> STComplexArray s -> ST s Unit

-- | According to the issue:
-- | https://github.com/indutny/fft.js/issues/10, the realTransform
-- | only fills the left half of the array with data. This function is
-- | then used to complete that. However, I find that the
-- | realTransform function gives the correct result and that I don't
-- | ever need to use this function.
foreign import completeSpectrum :: forall s. FFT -> STComplexArray s -> ST s Unit
