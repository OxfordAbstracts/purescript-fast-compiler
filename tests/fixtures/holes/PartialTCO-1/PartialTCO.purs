module Main where

import Prelude
import Effect.Console (log)
import Partial.Unsafe (unsafePartial)

main = do
  let _ = unsafePartial partialTCO true 1000000
  log "Done"

partialTCO :: Partial => Boolean -> Int -> Int
partialTCO true 0 = ?test
partialTCO true n = partialTCO true (n - 1)
