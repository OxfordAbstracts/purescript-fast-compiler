module Main where

import Prelude
import Effect.Console (log)

type X = String
type Y = X -> X

fn :: ?test
fn a = a

main = log (fn "Done")
