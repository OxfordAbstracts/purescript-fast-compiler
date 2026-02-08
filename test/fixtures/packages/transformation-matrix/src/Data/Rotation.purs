module Data.TransformationMatrix.Rotation where

import Prelude
import Data.Number (pi)

newtype Radians = Radians Number

degreeToRadians :: Number -> Radians
degreeToRadians n = Radians $ n * pi / 180.0
