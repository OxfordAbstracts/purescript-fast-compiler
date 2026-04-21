module Main where

import Prelude
import Effect.Console

infixl 4 what as ?!

what :: forall a b. a -> b -> a
what a _ = a

main = ?test $ "Done" ?! true
