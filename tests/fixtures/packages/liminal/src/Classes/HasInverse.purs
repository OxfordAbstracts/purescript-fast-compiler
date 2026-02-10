module Classes.HasInverse where

import Data.TransformationMatrix.Matrix4 (Matrix4)

class HasInverse m where
  getInverse :: m -> Matrix4
  setInverse :: Matrix4 -> m -> m