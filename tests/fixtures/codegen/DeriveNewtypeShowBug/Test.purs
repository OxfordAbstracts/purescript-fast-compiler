module Test where

import Prelude

type MyString = String

newtype X = X MyString

derive newtype instance showX :: Show X

-- TEST: "\"hello\""
test = show (X "hello")
