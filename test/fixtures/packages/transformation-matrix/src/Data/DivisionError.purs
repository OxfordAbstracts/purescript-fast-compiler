module Data.TransformationMatrix.DivisionError where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

data DivisionError = DivideByZero

derive instance genericDivisionError :: Generic DivisionError _

instance showDivisionError :: Show DivisionError where
  show = genericShow

derive instance eqDivisionError :: Eq DivisionError