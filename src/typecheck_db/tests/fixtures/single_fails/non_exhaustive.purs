module Test.NonExhaustive where

-- `Just` isn't covered — expect a NonExhaustive diagnostic.
data Maybe a = Nothing | Just a

unsafe :: forall a. Maybe a -> Int
unsafe Nothing = 0
