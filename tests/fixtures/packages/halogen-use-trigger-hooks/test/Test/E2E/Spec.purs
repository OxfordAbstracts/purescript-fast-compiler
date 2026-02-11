module Test.E2E.Spec where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Data.Array (fold)
import Data.Const (Const)
import Effect.Aff (Aff, Error)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (HalogenIO)
import Halogen as H
import Test.E2E.Environment (logShouldBe, testOnNextTick, testTriggerEval)
import Test.E2E.Environment as Environment
import Test.E2E.Logger (LoggerT, VirtualConsole, resetLog)
import Test.Spec (Spec, before, describe, it)
import Test.Utils.HTML (unsafeQuerySelector, unsafeToHTMLElement, (.>))
import Test.Utils.HTML as HTML
import Test.Utils.HappyDOM (waitUntilComplete)
import Web.DOM.Element (Element)
import Web.DOM.ParentNode (QuerySelector(..))
import Web.HTML (Window)
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window (document)

type TestEnv =
  { window :: Window
  , console :: VirtualConsole
  , io :: HalogenIO (Const Unit) Void Aff
  , elements :: { buttonEl :: Element }
  }

_app :: QuerySelector
_app = QuerySelector "#app"

_button :: QuerySelector
_button = QuerySelector "#button"

setup :: H.Component (Const Unit) {} Void (LoggerT Aff) -> Aff TestEnv
setup component = do
  { window, console, io } <- Environment.setup component
  pn <- liftEffect $ HTMLDocument.toParentNode <$> document window
  buttonEl <- unsafeQuerySelector (_app .> _button) pn
  pure
    { window
    , console
    , io
    , elements: { buttonEl }
    }

textContentShouldBe :: forall m a. MonadEffect m => MonadThrow Error m => Show a => Element -> a -> m Unit
textContentShouldBe el = show >>> (el `HTML.textContentShouldBe` _)

spec :: Spec Unit
spec = describe "module Halogen.UseTrigger" do
  let
    click' window el = do
      htmlEl <- unsafeToHTMLElement el
      liftEffect $ HTMLElement.click htmlEl
      waitUntilComplete window

  before (setup testTriggerEval) do
    describe "triggerEval" do
      it "should trigger re-render" \{ window, io, console, elements: { buttonEl } } -> do
        let
          logAfterTick = [ "Tick" ]
          click = click' window

        resetLog console
        console `logShouldBe` []

        click buttonEl
        console `logShouldBe` logAfterTick

        click buttonEl
        console `logShouldBe` fold [ logAfterTick, logAfterTick ]

        click buttonEl
        console `logShouldBe` fold [ logAfterTick, logAfterTick, logAfterTick ]

        io.dispose :: Aff Unit

  before (setup testOnNextTick) do
    describe "onNextTick" do
      it "should executed on next tick" \{ window, io, console, elements: { buttonEl } } -> do
        let
          logTickEffect n = "[TickEffect] " <> show n
          logOnNextTick n = "[onNextTick] " <> show n
          click = click' window

        console `logShouldBe`
          [ logTickEffect 0 ]

        click buttonEl
        console `logShouldBe`
          [ logTickEffect 0
          , logTickEffect 1
          ]

        click buttonEl
        console `logShouldBe`
          [ logTickEffect 0
          , logTickEffect 1
          , logOnNextTick 0
          , logTickEffect 2
          ]

        io.dispose :: Aff Unit

