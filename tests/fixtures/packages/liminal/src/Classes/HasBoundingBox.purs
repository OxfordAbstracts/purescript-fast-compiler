module Classes.HasBoundingBox where

import Data.Geometry.BoundingBox (BoundingBox)

class HasBoundingBox m where
  getBoundingBox :: m -> BoundingBox
