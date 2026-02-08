module Test.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (try)
import Node.Process.Environment (Environment(..), detect, lookup, require)
import Test.Fixtures.Environment (set, unset)
import Test.Fixtures.Errors (read)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main ∷ Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "lookup" do
    it "looks up an environment variable" do
      set "EXAMPLE" "..."
      env ← lookup "EXAMPLE" "fallback"
      env `shouldEqual` "..."

    it "defaults to a fallback if the environment variable is missing" do
      unset "EXAMPLE"
      env ← lookup "EXAMPLE" "fallback"
      env `shouldEqual` "fallback"

  describe "require" do
    it "looks up an environment variable" do
      set "EXAMPLE" "..."
      env ← require "EXAMPLE"
      env `shouldEqual` "..."

    it "throws an error if the environment variable is missing" do
      unset "EXAMPLE"
      error ← try $ require "EXAMPLE"
      read error `shouldEqual` Just "Missing environment variable: EXAMPLE"

  describe "detect" do
    it "parses the NODE_ENV" do
      set "NODE_ENV" "production"
      env ← detect
      env `shouldEqual` Production

    it "throws an error if the NODE_ENV is not recognised" do
      set "NODE_ENV" "..."
      error ← try detect
      read error `shouldEqual` Just "Not a valid environment: ..."

    it "throws an error if the NODE_ENV is missing" do
      unset "NODE_ENV"
      error ← try detect
      read error `shouldEqual` Just "Missing environment variable: NODE_ENV"
