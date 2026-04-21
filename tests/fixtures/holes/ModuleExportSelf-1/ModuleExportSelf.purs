module Main where

import Effect.Console
import A

bar :: Foo
bar = ?test

main = do
  logShow (show bar)
  log "Done"
