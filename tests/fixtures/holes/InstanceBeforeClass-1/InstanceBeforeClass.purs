module Main where

import Prelude
import Effect.Console (log)

instance fooNumber :: Foo Number where
  foo = ?test

class Foo a where
  foo :: a

main = log "Done"
