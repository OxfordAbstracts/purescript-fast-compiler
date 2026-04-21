module Main where

import Prelude
import Def (what)
import Effect.Console

infixl 4 what as ?!

main = ?test $ "Done" ?! true
