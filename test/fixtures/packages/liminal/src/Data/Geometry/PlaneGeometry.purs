module Data.Geometry.PlaneGeometry where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.TransformationMatrix.Vector3 (Vector3(..))
import Data.Vector.Vector4 (Vector4(..))

newtype PlaneGeometry = PlaneGeometry { xspan :: Number, yspan :: Number }

derive instance genericPlaneGeometry :: Generic PlaneGeometry _

instance showPlaneGeometry :: Show PlaneGeometry where
  show = genericShow

derive instance eqPlaneGeometry :: Eq PlaneGeometry

derive instance ordPlaneGeometry :: Ord PlaneGeometry

planeGeometry :: { height :: Number, width :: Number } -> PlaneGeometry
planeGeometry { height, width } = PlaneGeometry { xspan: width, yspan: height }

calculateVertices
  :: PlaneGeometry
  -> Vector3 Number
  -> Vector4 (Vector3 Number)
calculateVertices (PlaneGeometry { xspan, yspan }) (Vector3 x y z) = vertices
  where
  halfXspan = xspan / 2.0
  halfYspan = yspan / 2.0
  vertices = Vector4
    (Vector3 (x - halfXspan) (y + halfYspan) z)
    (Vector3 (x + halfXspan) (y + halfYspan) z)
    (Vector3 (x - halfXspan) (y - halfYspan) z)
    (Vector3 (x + halfXspan) (y - halfYspan) z)
