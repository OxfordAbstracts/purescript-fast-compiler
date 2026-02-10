module Data.Geometry.Geometry where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Geometry.BoxGeometry (BoxGeometry)
import Data.Geometry.LineGeometry (LineGeometry)
import Data.Geometry.PlaneGeometry (PlaneGeometry)
import Data.Geometry.SphereGeometry (SphereGeometry)

data Geometry
  = GeometryBox BoxGeometry
  | GeometrySphere SphereGeometry
  | GeometryPlane PlaneGeometry
  | GeometryLine LineGeometry

derive instance genericGeometry :: Generic Geometry _

instance showGeometry :: Show Geometry where
  show = genericShow

derive instance eqGeometry :: Eq Geometry

derive instance ordGeometry :: Ord Geometry