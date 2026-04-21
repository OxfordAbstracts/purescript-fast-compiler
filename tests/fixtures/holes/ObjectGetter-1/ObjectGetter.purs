module Main where

import Prelude
import Effect.Console (log, logShow)

getX = _.x

point = ?test

main = do
  logShow $ getX point
  log $ _." 123 string Prop Name " { " 123 string Prop Name ": "OK" }
  log $ (_.x >>> _.y) { x: { y: "Nested" } }
  log $ _.value { value: "Done" }
