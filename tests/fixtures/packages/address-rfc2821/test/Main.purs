module Test.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

import Test.Data.RFC2821.Spec (spec)

main :: Effect Unit
main = launchAff_ do
  runSpec [consoleReporter] spec
