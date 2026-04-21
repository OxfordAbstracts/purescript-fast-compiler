module Main where

import Prelude
import Effect.Console (log)

length :: forall a. Array a -> Int
length _ = 0

type Foo a = Array a

foo _ = ?test

main = log "Done"
