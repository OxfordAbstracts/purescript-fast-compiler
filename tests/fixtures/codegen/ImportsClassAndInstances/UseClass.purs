module UseClass where

import MyClass (class MyShow, myShow)

showThing :: forall a. MyShow a => a -> String
showThing x = myShow x

showInt :: String
showInt = myShow 42
