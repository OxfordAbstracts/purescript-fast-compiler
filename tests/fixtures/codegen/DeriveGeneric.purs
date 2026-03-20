module DeriveGeneric where

import Data.Generic.Rep (class Generic)

data Maybe a = Nothing | Just a

derive instance genericMaybe :: Generic (Maybe a) _

data Color = Red | Green | Blue

derive instance genericColor :: Generic Color _
