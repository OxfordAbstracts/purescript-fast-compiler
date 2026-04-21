module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)

class Foo a where
  foo :: (String -> a ((Unit)))

instance fooLogEff :: Foo Effect where
  foo = ?test

main :: Effect Unit
main = foo "Done"
