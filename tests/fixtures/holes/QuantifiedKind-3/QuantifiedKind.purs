module Main where

import Effect.Console (log)

data Proxy a = Proxy

test :: forall k (a :: k). Proxy ?test
test = Proxy

main = log "Done"
