module Test.Main where

import Prelude
import Data.Complex.FFT (Direction(..), fft)
import Data.Complex (Cartesian(..), magnitudeSquared)
import Data.Foldable (sum)
import Data.Int (toNumber)
import Data.Number (sin, pi)
import Data.Array ((..))

import Effect (Effect)
import Effect.Class.Console (log)

nSamples = 128 :: Int
te = 0.01 :: Number  -- seconds

sr = 1.0 / te :: Number  -- hertz
fe = sr / toNumber (nSamples-1) :: Number  -- hertz
period = 1.0 / fe :: Number  -- seconds

five = 5.0 :: Number  -- hertz

c1 :: Number -> Int -> Cartesian Number
c1 f i = Cartesian (sin (2.0 * pi * f * toNumber i * te)) (toNumber 0)

main :: Effect Unit
main = do
  let signal = (\i -> c1 five i) <$> (0..(nSamples-1))
  let spectrum = fft Forward signal
  log $ show $ sum $ magnitudeSquared <$> spectrum
  log $ show $ sum $ magnitudeSquared <$> fft Backward spectrum

