module Main where

import Effect.Console (log)

-- Pattern guard with irrefutable record binding should be treated as
-- always-true for exhaustiveness, covering the remaining array cases.
classify :: Array Int -> Int
classify [] = ?test
classify [_] = 1
classify [_, _] = 2
classify ns
  | { len } <- { len: 3 } = len

main = log "Done"
