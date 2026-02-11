module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Data.EtaConversionTransformerSpec (spec) 
import Test.Data.ReaderTEtaConversionTransformerSpec as ReaderTTransformer
import Test.Data.ArgsRotaterSpec as ArgsRotater
import Test.Spec.Reporter (specReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = launchAff_ $ runSpec [ specReporter ] do
  spec
  ReaderTTransformer.spec
  ArgsRotater.spec
