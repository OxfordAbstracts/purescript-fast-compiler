module Data.Geometry.Ray where

import Prelude
import Data.TransformationMatrix.Vector3 (Vector3)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

data Ray = Ray (Vector3 Number) (Vector3 Number)

derive instance genericRay :: Generic Ray _

instance showRay :: Show Ray where
  show = genericShow
