module Main where

import Effect.Console (log)

data T a = T

ti :: ?test Int
ti = T

t :: forall a. T a
t = T

xs = [ti, t, t]

main = log "Done"
