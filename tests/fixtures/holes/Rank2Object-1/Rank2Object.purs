module Main where

import Prelude
import Effect.Console

data Foo = Foo { id :: forall a. a -> a }

foo :: Foo -> Number
foo (Foo { id: f }) = ?test

main = log "Done"
