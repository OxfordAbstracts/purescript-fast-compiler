module Test.Main where

import Effect        ( Effect )
import Prelude
import Test.Encoding ( testEncoding )

main :: Effect Unit
main = do
  testEncoding
