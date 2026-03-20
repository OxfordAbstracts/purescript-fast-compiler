module Main where

import Effect.Console (log)

type Input = { x :: Int, y :: String }

-- Record patterns are irrefutable and should not trigger
-- non-exhaustive pattern warnings even when a data type
-- with the same name exists in data_constructors.
getX :: Input -> Int
getX { x } = x

main = log "Done"
