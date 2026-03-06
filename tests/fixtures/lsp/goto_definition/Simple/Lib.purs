module Simple.Lib where

import Prelude

class Cl a where
  member :: a -> a

data LibT
  = LibA
  | LibB

times2 n = n * 2
