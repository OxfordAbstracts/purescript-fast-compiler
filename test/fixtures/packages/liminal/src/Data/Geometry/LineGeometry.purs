module Data.Geometry.LineGeometry where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.TransformationMatrix.Vector3 (Vector3(..))
import Data.TransformationMatrix.Vector2 (Vector2(..))

newtype LineGeometry = LineGeometry { yspan :: Number }

derive instance genericLineGeometry :: Generic LineGeometry _

instance showLineGeometry :: Show LineGeometry where
  show = genericShow

derive instance eqLineGeometry :: Eq LineGeometry

derive instance ordLineGeometry :: Ord LineGeometry

lineGeometry :: Number -> LineGeometry
lineGeometry length = LineGeometry { yspan: length }

-- This implementation is dependent on how threejs creates a LineGeometry(y-span)
-- There is no "lateral depth" or "forward back depth" in the x and z-dimensions on creation. We create the positions of the
-- vertices as if the Line was in its newly created state, then we apply the Line's
-- transformation matrix to each vertex. 
calculateVertices
  :: LineGeometry
  -> Vector3 Number
  -> Vector2 (Vector3 Number)
calculateVertices (LineGeometry { yspan }) (Vector3 x y z) = vertices
  where
  halfYspan = yspan / 2.0
  vertices = Vector2
    (Vector3 x (y + halfYspan) z)
    (Vector3 x (y - halfYspan) z)
