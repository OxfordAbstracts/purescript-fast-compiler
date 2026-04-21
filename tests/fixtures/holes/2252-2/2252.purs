module Main where

import Effect.Console (log)

data T a = T

ti :: T Int
ti = T

t :: forall a. T a
t = T

xs = [?test, t, t]

main = log "Done"
