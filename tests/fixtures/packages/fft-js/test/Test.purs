module Test.Main where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Number (abs)
import Data.Traversable (traverseDefault)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console as Console
import Effect.Exception (throw)
import Effect.Random (randomRange)
import FFT (RealArray(..), ComplexArray(..))
import FFT as FFT
import FFT.Complex (toComplexArray, fromComplexArray)
import Test.FFT as MyFFT


-- | We want to check if the two arrays are equal up to a floating
-- | point error
myArrayEq :: Array Number -> Array Number -> Tuple Boolean Int
myArrayEq arr1 arr2 =
  foldl (\(Tuple prevBool prevInt) (Tuple a b) -> Tuple (prevBool && (abs (a - b) < 10e-7)) $ if prevBool == false then prevInt - 1 else prevInt + 1) (Tuple true 0) (Array.zip arr1 arr2)


randomArray2048 :: Effect (Array Number)
randomArray2048 =
  traverseDefault (\_ -> randomRange (-2048.0) 2048.0) (Array.replicate 2048 0)

randomArray4096 :: Effect (Array Number)
randomArray4096 =
  traverseDefault (\_ -> randomRange (-2048.0) 2048.0) (Array.replicate 4096 0)

realTest :: Effect Boolean
realTest = do
  initArray <- randomArray2048
  let fft = FFT.makeFFT 2048
      ComplexArray transformedArray = FFT.realTransform fft $ RealArray initArray
      ComplexArray myTransformedArray = toComplexArray $ MyFFT.fourierNumbers initArray
  let Tuple result indx = myArrayEq myTransformedArray transformedArray
  if result
    then pure true
    else do
    Console.log $ "Initial array: " <> show initArray <> "\n"
    Console.log $ "fft.js array: " <> show transformedArray <> "\n"
    Console.log $ "my fft array: " <> show myTransformedArray <> "\n"
    _ <- throw $ "Real valued ffts don't match at position: " <> show indx
    pure false

complexTest :: Effect Boolean
complexTest = do
  initArray <- randomArray4096
  let fft = FFT.makeFFT 2048
      ComplexArray transformedArray = FFT.transform fft $ ComplexArray initArray
      ComplexArray myTransformedArray = toComplexArray <<< MyFFT.fourier <<< fromComplexArray $ ComplexArray initArray
  let Tuple result indx = myArrayEq myTransformedArray transformedArray
  if result
    then pure true
    else do
    Console.log $ "Initial array: " <> show initArray <> "\n"
    Console.log $ "fft.js array: " <> show transformedArray <> "\n"
    Console.log $ "my fft array: " <> show myTransformedArray <> "\n"
    _ <- throw $ "Complex valued ffts don't match at position: " <> show indx
    pure false

inverseTest :: Effect Boolean
inverseTest = do
  initArray <- randomArray4096
  let fft = FFT.makeFFT 2048
      array = FFT.transform fft $ ComplexArray initArray
      ComplexArray invArray = FFT.inverseTransform fft array
  let Tuple result indx = myArrayEq initArray invArray
  if result
    then pure true
    else do
    Console.log $ "Initial array: " <> show initArray <> "\n"
    Console.log $ "Transformed array " <> show array <> "\n"
    Console.log $ "Inversed: " <> show invArray <> "\n"
    _ <- throw $ "Complex valued ffts don't match at position:" <> show indx
    pure false

main :: Effect Unit
main = do
  Console.log $ "Running real test..."
  realTestResult <- realTest
  Console.log $ "Real test result: " <> show realTestResult <> "\n"

  Console.log $ "Running complex test..."
  complexTestResult <- complexTest
  Console.log $ "Complex test result: " <> show complexTestResult <> "\n"

  Console.log $ "Running inverse test..."
  inverseTestResult <- inverseTest
  Console.log $ "Inverse test result: " <> show inverseTestResult <> "\n"
