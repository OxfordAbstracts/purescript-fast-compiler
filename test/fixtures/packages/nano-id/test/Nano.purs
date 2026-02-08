module Test.Main where

import Prelude

import Data.Maybe (fromMaybe)
import Data.String (length)
import Data.String.Utils (repeat)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Nano (create, createDefault)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  describe "Attributes" do
    it "produces the correct length" do
      let 
        size = 12
        alphabet = "a"
      nanoid <- liftEffect (create alphabet size)
      length (fromMaybe "" nanoid) `shouldEqual` size
    it "should only contain values from the alphabet" do
      let 
        size = 20
        alphabet = "a"
        output = (repeat size "a")
      nanoid <- liftEffect (create alphabet size)
      nanoid `shouldEqual` output
    it "should produce a default nanoid when no arguments specified" do
      nanoid <- liftEffect createDefault
      length (fromMaybe "" nanoid) `shouldEqual` 21
