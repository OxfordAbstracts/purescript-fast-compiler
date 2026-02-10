module Data.TransformationMatrix.Spherical where

import Prelude
import Data.TransformationMatrix.Vector3 (Vector3(..), length)
import Data.Number (sin, cos, atan2, acos)
import Data.Either (Either)
import Data.TransformationMatrix.DivisionError (DivisionError)
import Data.TransformationMatrix.Division (divide)

data Spherical = Spherical Number SphericalAngles

data SphericalAngles = SphericalAngles Number Number

sphericalAnglesToVector3
  :: Spherical
  -> Vector3 Number
sphericalAnglesToVector3 (Spherical radius (SphericalAngles theta phi)) = Vector3 x y z
  where
  sinPhiRadius = (sin phi) * radius
  x = sinPhiRadius * (sin theta)
  y = (cos phi) * radius
  z = sinPhiRadius * (cos theta)

vector3ToSpherical
  :: Vector3 Number
  -> Either DivisionError Spherical
vector3ToSpherical offset@(Vector3 x y z) = do
  let
    radius = length offset
    theta = atan2 x z
  phi <- acos <$> divide y radius
  pure $ Spherical radius $ SphericalAngles theta phi