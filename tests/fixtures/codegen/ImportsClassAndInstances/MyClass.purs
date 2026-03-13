module MyClass where

class MyShow a where
  myShow :: a -> String

instance myShowInt :: MyShow Int where
  myShow _ = "int"

instance myShowString :: MyShow String where
  myShow s = s
