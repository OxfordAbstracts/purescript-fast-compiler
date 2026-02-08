module Data.TransformationMatrix.RotationMatrix where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.TransformationMatrix.Vector3 (Vector3(..), normalize, subtract, crossProduct)
import Data.Either (Either)
import Data.TransformationMatrix.DivisionError (DivisionError)
import Data.Number (sin, cos)
import Data.TransformationMatrix.Rotation (Radians(..))

data RotationMatrix = RotationMatrix
  Number
  Number
  Number
  Number
  Number
  Number
  Number
  Number
  Number

derive instance genericRotationMatrix :: Generic RotationMatrix _
instance showRotationMatrix :: Show RotationMatrix where
  show = genericShow

derive instance eqRotationMatrix :: Eq RotationMatrix

up :: Vector3 Number
up = Vector3 0.0 1.0 0.0

lookAtRotation
  :: Vector3 Number
  -> Vector3 Number
  -> Either DivisionError RotationMatrix
lookAtRotation eye target = do
  zAxis@(Vector3 zAxisX zAxisY zAxisZ) <- normalize $ (subtract eye target)
  xAxis@(Vector3 xAxisX xAxisY xAxisZ) <- normalize $ (crossProduct up zAxis)
  (Vector3 yAxisX yAxisY yAxisZ) <- normalize $ (crossProduct zAxis xAxis)
  pure $ RotationMatrix
    xAxisX
    yAxisX
    zAxisX
    xAxisY
    yAxisY
    zAxisY
    xAxisZ
    yAxisZ
    zAxisZ

xAxisRotation
  :: Radians
  -> RotationMatrix
xAxisRotation (Radians radians) = RotationMatrix
  1.0
  0.0
  0.0
  0.0
  (cos radians)
  (-(sin radians))
  0.0
  (sin radians)
  (cos radians)

yAxisRotation
  :: Radians
  -> RotationMatrix
yAxisRotation (Radians radians) = RotationMatrix
  (cos radians)
  0.0
  (-(sin radians))
  0.0
  1.0
  0.0
  (sin radians)
  0.0
  (cos radians)

zAxisRotation
  :: Radians
  -> RotationMatrix
zAxisRotation (Radians radians) = RotationMatrix
  (cos radians)
  (-(sin radians))
  0.0
  (sin radians)
  (cos radians)
  0.0
  0.0
  0.0
  1.0