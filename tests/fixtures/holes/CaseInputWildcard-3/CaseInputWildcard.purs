module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)

data Foo = X | Y

what ∷ Foo → Int → Boolean → Foo
what x = case _, x, _ of
  0, X, true → X
  0, Y, true → X
  _, _, _ → Y

main :: Effect ?test
main = do
  let tmp = what Y 0 true
  log "Done"
