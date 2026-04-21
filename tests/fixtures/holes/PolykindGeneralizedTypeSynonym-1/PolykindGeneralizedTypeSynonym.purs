module Main where

import Effect.Console (log)

data Proxy a = Proxy

type Prozy = Proxy

test1 = Proxy :: Prozy Int
test2 = ?test

main = log "Done"
