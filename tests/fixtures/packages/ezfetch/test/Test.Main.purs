module Test.Main where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (specReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Effect.Aff.HTTP.Form as Test.Form

main :: Effect Unit
main = runSpecAndExitProcess [ specReporter ] do
  Test.Form.spec
