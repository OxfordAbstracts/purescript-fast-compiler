module Main where

import Effect.Console (log)

-- First argument needs to be `k`.
type F k t = forall proxy. proxy k -> t

test :: F Symbol Int
test _ = ?test

main = log "Done"
