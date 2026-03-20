module ShowClass where

class MyShow a where
  myShow :: a -> String

instance myShowInt :: MyShow Int where
  myShow _ = "int"

instance myShowString :: MyShow String where
  myShow s = s

instance myShowBoolean :: MyShow Boolean where
  myShow b = case b of
    true -> "true"
    false -> "false"
