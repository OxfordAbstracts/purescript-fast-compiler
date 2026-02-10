module Data.Geometry.BoxGeometry where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Vector.Vector8 (Vector8(..))
import Data.TransformationMatrix.Vector3 (Vector3(..))
import Data.Geometry.BoundingBox (BoundingBox(..))

newtype BoxGeometry = BoxGeometry { xspan :: Number, yspan :: Number, zspan :: Number }

derive instance genericBoxGeometry :: Generic BoxGeometry _

instance showBoxGeometry :: Show BoxGeometry where
  show = genericShow

derive instance eqBoxGeometry :: Eq BoxGeometry

derive instance ordBoxGeometry :: Ord BoxGeometry

boxGeometry :: { length :: Number, width :: Number, thickness :: Number } -> BoxGeometry
boxGeometry { length, width, thickness } = BoxGeometry { xspan: width, yspan: length, zspan: thickness }

calculateVertices
  :: BoxGeometry
  -> Vector3 Number
  -> Vector8 (Vector3 Number)
calculateVertices (BoxGeometry { xspan, yspan, zspan }) (Vector3 x y z) = vertices
  where
  halfXspan = xspan / 2.0
  halfYspan = yspan / 2.0
  halfZspan = zspan / 2.0
  vertices = Vector8
    (Vector3 (x - halfXspan) (y + halfYspan) (z + halfZspan))
    (Vector3 (x + halfXspan) (y + halfYspan) (z + halfZspan))
    (Vector3 (x - halfXspan) (y - halfYspan) (z + halfZspan))
    (Vector3 (x + halfXspan) (y - halfYspan) (z + halfZspan))
    (Vector3 (x - halfXspan) (y + halfYspan) (z - halfZspan))
    (Vector3 (x + halfXspan) (y + halfYspan) (z - halfZspan))
    (Vector3 (x - halfXspan) (y - halfYspan) (z - halfZspan))
    (Vector3 (x + halfXspan) (y - halfYspan) (z - halfZspan))

calculateBoundingBox
  :: BoxGeometry
  -> Vector3 Number
  -> BoundingBox
calculateBoundingBox (BoxGeometry { xspan, yspan, zspan }) (Vector3 x y z) = BoundingBox min max
  where
  halfXspan = xspan / 2.0
  halfYspan = yspan / 2.0
  halfZspan = zspan / 2.0
  min = Vector3 (x - halfXspan) (y - halfYspan) (z - halfZspan)
  max = Vector3 (x + halfXspan) (y + halfYspan) (z + halfZspan)
