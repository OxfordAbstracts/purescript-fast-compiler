module Main where

import Prelude
import Prelude as P
import Effect.Console

f :: forall a. a -> ?test
f = P.identity

main = P.($) log ((f P.<<< f) "Done")
