module Main where

import Prelude
import Effect.Console (log)

data Maybe a = Nothing | Just a

test :: forall a. Maybe ?test -> Maybe a
test m = o.x
  where
    o = case m of Nothing -> { x : Nothing }
                  Just a  -> { x : Just a }

main = log "Done"
