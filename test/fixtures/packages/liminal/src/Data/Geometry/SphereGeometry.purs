module Data.Geometry.SphereGeometry where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

newtype SphereGeometry = SphereGeometry { radius :: Number }

derive instance genericSphereGeometry :: Generic SphereGeometry _

instance showSphereGeometry :: Show SphereGeometry where
  show = genericShow

derive instance eqSphereGeometry :: Eq SphereGeometry

derive instance ordSphereGeometry :: Ord SphereGeometry
