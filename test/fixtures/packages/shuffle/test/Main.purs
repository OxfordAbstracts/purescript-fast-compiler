module Test.Main where

import Prelude

import Data.Array.NonEmpty (singleton)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse_)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Shuffle (pick, pickMonoid, pickNonEmpty, pickOr, shuffle)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldContain, shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

empty ∷ Array String
empty = []

alphabet ∷ Array String
alphabet = [ "a", "b", "c", "d", "e" ]

main ∷ Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "shuffle" do
    it "shuffles an array" do
      shuffled ← liftEffect $ shuffle alphabet
      traverse_ (shouldContain shuffled) alphabet

  describe "pick" do
    it "picks an element from an array" do
      picked ← liftEffect $ pick alphabet
      map Just alphabet `shouldContain` picked

    it "defaults to a Nothing for an empty array" do
      picked ← liftEffect $ pick empty
      picked `shouldEqual` Nothing

  describe "pickOr" do
    it "defaults to a fallback for an empty array" do
      picked ← liftEffect <<< pickOr "_" $ empty
      picked `shouldEqual` "_"

  describe "pickMonoid" do
    it "defaults to mempty for an empty array" do
      picked ← liftEffect $ pickMonoid empty
      picked `shouldEqual` ""

  describe "pickNonEmpty" do
    it "picks an element from a non-empty array" do
      picked ← liftEffect <<< pickNonEmpty $ singleton "a"
      picked `shouldEqual` "a"
