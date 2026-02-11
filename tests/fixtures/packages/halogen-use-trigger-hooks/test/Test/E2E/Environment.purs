module Test.E2E.Environment where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Data.Array as Array
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff (Aff, Error)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Halogen (HalogenIO)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.Hooks (captures, useState, useTickEffect)
import Halogen.Hooks as Hooks
import Halogen.UseTrigger (useTrigger)
import Halogen.VDom.Driver (runUI)
import Test.E2E.Logger (class MonadLogger, Logger, VirtualConsole, runLoggerT, writeLogLn)
import Test.Spec.Assertions (shouldEqual)
import Test.Utils.HappyDOM as HappyDOM
import Web.HTML (Window)
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.Window (document)

type Env q o =
  { io :: HalogenIO q o Aff
  , window :: Window
  , console :: VirtualConsole
  }

setup :: forall q o. H.Component q {} o Logger -> Aff (Env q o)
setup app' = do
  window <- liftEffect HappyDOM.window
  mbBody <- liftEffect (HTMLDocument.body =<< document window)
  case mbBody of
    Just body -> do
      console <- liftEffect $ Ref.new Nil
      io <- runUI (H.hoist (runLoggerT console) app') {} body
      pure { io, window, console }
    Nothing -> liftEffect $ throw "Failed to setup test environment."

testTriggerEval :: forall q i o m. MonadEffect m => MonadLogger m => H.Component q i o m
testTriggerEval = Hooks.component \_ _ -> Hooks.do
  { triggerEval } <- useTrigger

  captures {} useTickEffect do
    writeLogLn "Tick"
    pure Nothing

  Hooks.pure do
    HH.div [ HP.id "app" ]
      [ HH.button
          [ HP.id "button"
          , HE.onClick \_ -> triggerEval
          ]
          [ HH.text "FIRE" ]
      ]

testOnNextTick :: forall q i o m. MonadEffect m => MonadLogger m => H.Component q i o m
testOnNextTick = Hooks.component \_ _ -> Hooks.do
  { onNextTick } <- useTrigger
  _ /\ countId <- useState 0

  captures {} useTickEffect do
    Hooks.get countId >>= \cnt -> do
      writeLogLn $ "[TickEffect] " <> show cnt
    pure Nothing

  let
    handleIncrClick = do
      cnt <- Hooks.get countId
      Hooks.put countId (cnt + 1)
      onNextTick \_ -> do
        writeLogLn $ "[onNextTick] " <> show cnt

  Hooks.pure do
    HH.div [ HP.id "app" ]
      [ HH.button
          [ HP.id "button"
          , HE.onClick \_ -> handleIncrClick
          ]
          [ HH.text "Incr" ]
      ]

logShouldBe :: forall m. MonadEffect m => MonadThrow Error m => VirtualConsole -> Array String -> m Unit
logShouldBe vc expect = do
  log <- liftEffect $ Array.fromFoldable <$> Ref.read vc
  log `shouldEqual` expect