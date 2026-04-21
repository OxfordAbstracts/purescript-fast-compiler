module Main where

import Prelude
import Effect.Console (log)

foo :: ?test
foo = """foo"""

main = log "Done"
