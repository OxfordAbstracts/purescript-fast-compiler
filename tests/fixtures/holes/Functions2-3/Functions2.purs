module Main where

import Prelude
import Test.Assert
import Effect.Console (log)

test :: forall a b. ?test -> b -> a
test = \const _ -> const

main = do
  let value = test "Done" {}
  assert' "Not done" $ value == "Done"
  log "Done"
