module Main where

import Prelude
import Effect.Console (log)

data Foo a = Foo

foo = \f -> case f of Foo -> "foo"

main = ?test "Done"
