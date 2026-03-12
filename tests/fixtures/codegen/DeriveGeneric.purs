module DeriveGeneric where

class Generic a rep | a -> rep

data Maybe a = Nothing | Just a

derive instance genericMaybe :: Generic (Maybe a) _

data Color = Red | Green | Blue

derive instance genericColor :: Generic Color _
