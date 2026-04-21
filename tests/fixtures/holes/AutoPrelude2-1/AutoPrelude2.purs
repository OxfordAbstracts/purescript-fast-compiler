module Main where

import Prelude
import Prelude as P
import Effect.Console

f :: forall a. a -> a
f = ?test

main = P.($) log ((f P.<<< f) "Done")
