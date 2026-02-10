module Test.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Vector3Spec (vector3Spec)
import Test.DivisionSpec (divisionSpec)
import Test.Matrix4Spec (matrix4Spec)

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  vector3Spec
  divisionSpec
  matrix4Spec
