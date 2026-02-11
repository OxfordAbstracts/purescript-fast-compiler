module Test.Main where

import Prelude

import Data.XML.PrettyPrintSpec (prettyPrintSpec)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec.Reporter (specReporter)
import Test.Spec.Reporter.Xunit (xunitReporter, defaultOptions)
import Test.Spec.Reporter.XunitSpec (xunitSpec)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = launchAff_ $ runSpec reporters do
  xunitSpec
  prettyPrintSpec

  where
    reporters =
      [ specReporter
      , xunitReporter (defaultOptions { outputPath = "output/test.xml" } )
      ]
