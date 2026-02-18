module InstanceDictionaries where

class MyShow a where
  myShow :: a -> String

instance myShowInt :: MyShow Int where
  myShow _ = "int"

instance myShowString :: MyShow String where
  myShow s = s

showValue :: forall a. MyShow a => a -> String
showValue x = myShow x
