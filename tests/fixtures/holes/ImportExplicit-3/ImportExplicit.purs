module Main where

import M1 (X(..))
import Effect.Console (log)

testX :: ?test
testX = X
testY = Y

main = log "Done"
