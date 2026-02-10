module Test.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Pipes.CBOR as Test.Pipes.CBOR
import Test.Spec.Reporter (specReporter)
import Test.Spec.Runner (defaultConfig, runSpec')

main :: Effect Unit
main = launchAff_ $ runSpec' (defaultConfig { failFast = true, timeout = Nothing }) [ specReporter ] do
  Test.Pipes.CBOR.spec
