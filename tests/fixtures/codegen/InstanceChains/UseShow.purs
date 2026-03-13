module UseShow where

import ShowClass (class MyShow, myShow)

showInt :: String
showInt = myShow 42

showStr :: String
showStr = myShow "hello"

showBool :: String
showBool = myShow true
