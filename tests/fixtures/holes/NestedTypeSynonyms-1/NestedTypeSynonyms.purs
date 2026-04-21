module Main where

import Prelude
import Effect.Console (log)

type X = String
type Y = X -> X

fn :: Y
fn a = ?test

main = log (fn "Done")
