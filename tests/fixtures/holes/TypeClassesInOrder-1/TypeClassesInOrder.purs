module Main where

import Prelude
import Effect.Console (log)

class Foo a where
  foo :: a -> String

instance fooString :: Foo String where
  foo s = ?test

main = log $ foo "Done"
