module Test.Main where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Aff (launchAff_, message, try)
import Elmish ((<?|))
import Elmish.Component (ComponentDef)
import Elmish.Enzyme (at, children, clickOn, exists, find, findAll, length, mapEach, prop, simulate', testComponent, testElement, text, (>>))
import Elmish.Enzyme as Enzyme
import Elmish.Enzyme.Adapter as Adapter
import Elmish.Foreign (readForeign)
import Elmish.HTML.Styled as H
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Spec.Reporter.Spec (specReporter)
import Test.Spec.Runner (runSpec)

foreign import _configureJsDomViaFfi :: Type

main :: Effect Unit
main = launchAff_ $ do
  adapter <- Adapter.unofficialReact_17
  liftEffect $ Enzyme.configure adapter
  runSpec [specReporter] spec

spec :: Spec Unit
spec = do
  describe "text" $
    it "returns text inside of the current element wrapper" $
      testElement (H.div "" "Foo") $
        text >>= shouldEqual "Foo"

  describe "find" do
    it "gets an element wrapper by a selector" $
      testComponent def $
        find ".bar" >> text >>= shouldEqual "Bar"
    it "crashes when multiple elements are found" $
      testComponent def $
        try (find ".qux p") >>= case _ of
          Left err -> message err `shouldEqual` "Expected a single element matching '.qux p', but found 3"
          Right _ -> fail "Expected find to crash"
    it "crashes when zero elements are found" $
      testComponent def $
        try (find ".qux a") >>= case _ of
          Left err -> message err `shouldEqual` "Expected a single element matching '.qux a', but found 0"
          Right _ -> fail "Expected find to crash"

  describe "findAll" $
    it "gets multiple elements" $
      testComponent def do
        findAll ".qux" >> length >>= shouldEqual 2
        findAll ".qux" >> findAll "p" >> length >>= shouldEqual 3
        findAll ".qux" >> findAll "p" >> at 0 >> text >>= shouldEqual "First"

  describe "exists" do
    it "returns `true` when selector is found" $
      testComponent def $
        exists ".bar" >>= shouldEqual true

    it "returns `false` when selector isn’t found" $
      testComponent def $
        exists ".not-found" >>= shouldEqual false

  describe "clickOn" $
    it "simulates a click event on a given selector" $
      testComponent def do
        find ".bar" >> text >>= shouldEqual "Bar"
        clickOn ".toggle-bar"
        exists ".bar" >>= shouldEqual false

  describe "prop" $
    it "returns the value of a given prop" $
      testElement (H.div_ "" { id: "blah" } H.empty) $
        prop "id" >>= shouldEqual "blah"

  describe "simulate'" $
    it "simulates a given event with the given argument on the current wrapper" $
      testComponent def do
        find ".baz" >> do
          prop "value" >>= shouldEqual ""
          simulate' "change" { target: { value: "New text" } }
        find ".baz" >> prop "value" >>= shouldEqual "New text"

  describe "children" do
    let
      elem =
        H.div ""
        [ H.div_ "" { id: "foo" } H.empty
        , H.div_ "" { id: "bar" } $ H.div_ "" { id: "bar-child" } H.empty
        , H.div_ "" { id: "baz" }
          [ H.div_ "" { id: "baz-child-1" } H.empty
          , H.div_ "" { id: "baz-child-2" } H.empty
          ]
        ]

    it "returns a wrapper containing the child nodes" $
      testElement elem $
        children >> mapEach (prop "id") >>= shouldEqual ["foo", "bar", "baz"]

    it "returns children of each node when called on many nodes" $
      testElement elem $
        children >> children >> mapEach (prop "id") >>= shouldEqual ["bar-child", "baz-child-1", "baz-child-2"]

-- Test Component

type State =
  { bar :: Boolean
  , baz :: String
  }

data Message
  = ToggleBar
  | ChangeBaz String

def :: ComponentDef Message State
def =
  { init: pure { bar: true, baz: "" }
  , update: \s -> case _ of
      ToggleBar -> pure s { bar = not s.bar }
      ChangeBaz baz -> pure s { baz = baz }
  , view: \s dispatch -> H.fragment
      [ H.div "foo" "Foo"
      , H.div "qux"
        [ H.p "" "First"
        , H.p "" "Second"
        ]
      , H.div "qux"
        [ H.p "" "Third"
        ]
      , if s.bar then
          H.div "bar" "Bar"
        else
          H.empty
      , H.button_ "toggle-bar" { onClick: dispatch ToggleBar } "Hide Bar"
      , H.input_ "baz"
          { onChange: dispatch <?| (map (ChangeBaz <<< _.target.value) <<< toEvent)
          , value: s.baz
          }
      ]
  }
  where
    toEvent :: _ -> _ { target :: { value :: String } }
    toEvent = readForeign
