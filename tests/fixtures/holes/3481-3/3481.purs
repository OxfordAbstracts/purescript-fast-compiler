module Main where

import Effect.Console (log)

message = { "0": { "1": "Done" }}

main = ?test message."0"."1"
