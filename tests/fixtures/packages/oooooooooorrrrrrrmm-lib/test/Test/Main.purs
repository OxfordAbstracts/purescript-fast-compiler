module Test.Main where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (notNull, null)
import Effect (Effect)
import Effect.Class.Console (log)
import Foreign (Foreign)
import OOOOOOOOOORRRRRRRMM.Lib (toValues, useMaybe)

vals :: Array Foreign
vals = toValues { "$1": 42, "$2": "hello" }

ret :: Array { id :: Int, name :: Maybe String }
ret = useMaybe [ { id: 42, name: notNull "hello" }, { id: 43, name: null } ]

main :: Effect Unit
main = do
  log "Tests are in the types!"
