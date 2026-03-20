module Base where

baseValue :: Int
baseValue = 1

identity :: forall a. a -> a
identity x = x
