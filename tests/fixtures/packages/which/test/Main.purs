module Test.Main where

import Prelude
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)
import Which (whichSync)

main :: Effect Unit
main = do
  let
    commandToFind = "spago"
  command <- whichSync Nothing commandToFind
  log
    $ case command of
        Just found -> "Found " <> commandToFind <> " at " <> found
        Nothing -> "Did not find " <> commandToFind
