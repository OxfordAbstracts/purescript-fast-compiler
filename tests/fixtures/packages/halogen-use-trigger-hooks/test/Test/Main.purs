module Test.Main where

import Prelude

import Effect (Effect)
import Halogen.UseTrigger.Internal (newEvalTrigger)
import Test.E2E.Spec as E2E
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Unsafe.Reference (unsafeRefEq)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Unit testing" do
    describe "evalTrigger" do
      it "should never be unsafely-referentially-equal to itself" do
        let
          trg1 = newEvalTrigger unit
          trg2 = newEvalTrigger unit
        unsafeRefEq trg1 trg2 `shouldEqual` false

  describe "E2E testing" do
    E2E.spec