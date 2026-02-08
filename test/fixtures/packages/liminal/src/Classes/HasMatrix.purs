module Classes.HasMatrix where

import Data.TransformationMatrix.Matrix4 (Matrix4)
import Data.TransformationMatrix.Vector3 (Vector3, subtract)

class HasMatrix m where
  getMatrix :: m -> Matrix4
  setMatrix :: Matrix4 -> m -> m
  getPosition :: m -> Vector3 Number
  setPosition :: Vector3 Number -> m -> m

subtractPositions
  :: forall a b
   . HasMatrix a
  => HasMatrix b
  => b
  -> a
  -> Vector3 Number
subtractPositions b a = subtract (getPosition b) (getPosition a)
