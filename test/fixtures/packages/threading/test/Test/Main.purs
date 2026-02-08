module Test.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Aff as Aff
import Test.Spec (it)
import Test.Spec.Reporter (specReporter)
import Test.Spec.Runner (defaultConfig, runSpec')
import Test.Threading.Barrier as Test.Threading.Barrier
import Test.Threading.Channel as Test.Threading.Channel
import Test.Threading.Data.Mutex as Test.Threading.Data.Mutex
import Test.Threading.Data.RWLock as Test.Threading.Data.RWLock

main :: Effect Unit
main = launchAff_ $ Aff.supervise $ runSpec' (defaultConfig { failFast = true, timeout = Nothing }) [ specReporter ] do
  Test.Threading.Data.Mutex.spec
  Test.Threading.Data.RWLock.spec
  Test.Threading.Channel.spec
  Test.Threading.Barrier.spec
  it "all tests were run" $ pure unit
