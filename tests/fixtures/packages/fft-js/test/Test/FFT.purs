module Test.FFT (class Indexable, index, length, range, fourierInt, fourierNumbers, fourierNumbersAbs, fourier) where

import Data.Complex (Cartesian(..), fromPolar, magnitudeSquared)
import Prelude
import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Number (sqrt, pi)

class Indexable a where
  index :: forall b. a b -> Int -> Maybe b
  length :: forall b. a b -> Int
  range :: Int -> Int -> a Int

instance Indexable Array where
  index = Array.index
  length = Array.length
  range = Array.range

fourierInt :: forall a. Indexable a => Applicative a => a Int -> a (Cartesian Number)
fourierInt arr = fourier ((\n -> Cartesian (toNumber n) 0.0) <$> arr)

fourierNumbers :: forall a. Indexable a => Applicative a => a Number -> a (Cartesian Number)
fourierNumbers arr = fourier ((\n -> Cartesian n 0.0) <$> arr)

fourierNumbersAbs :: forall a. Indexable a => Applicative a => a Number -> a Number
fourierNumbersAbs arr = sqrt <<< magnitudeSquared <$> (fourierNumbers arr)

fourier :: forall a. Indexable a => Applicative a => a (Cartesian Number) -> a (Cartesian Number)
fourier arr =
  case length arr of
    1 -> case index arr 0 of
      Just a -> pure a
      Nothing -> pure $ Cartesian 0.0 0.0
    _ ->
      let
        nEven n =
          arrGet arr (2 * n)

        nOdd n =
          arrGet arr (2 * n + 1)

        fourierEvens =
          fourier $ nEven <$> range 0 ((length arr `div` 2) - 1)

        fourierOdds =
          fourier $ nOdd <$> range 0 ((length arr `div` 2) - 1)

        twiddleFactor k =
          fromPolar 1.0 $ -2.0 * pi * toNumber k / (toNumber $ length arr)

        newGo n =
          ( arrGet fourierEvens
              (n `mod` (length arr `div` 2))
          )
            `add`
              ( twiddleFactor n
                  `mul`
                    (arrGet fourierOdds (n `mod` (length arr `div` 2)))
              )
      in
        newGo <$> range 0 (length arr - 1)
      where
      arrGet array n =
        case (index array n) of
          Just x -> x
          Nothing -> Cartesian 0.0 0.0
