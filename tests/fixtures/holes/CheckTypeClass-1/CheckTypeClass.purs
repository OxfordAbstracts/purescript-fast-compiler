module Main where

import Prelude
import Effect.Console (log)

data Bar a = Bar
data Baz

class Foo a where
  foo :: Bar a -> Baz

foo_ :: forall a. Foo a => a -> Baz
foo_ x = ?test

mkBar :: forall a. a -> Bar a
mkBar _ = Bar

main = log "Done"
