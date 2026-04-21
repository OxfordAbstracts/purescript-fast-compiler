module Main where

import Prelude
import Eg (Foo'(Bar'), (:->))
import Effect (Effect)
import Effect.Console (log)

bar' :: Foo'
bar' = ?test

main :: Effect Unit
main = case bar' of Bar' l r -> log "Done"
