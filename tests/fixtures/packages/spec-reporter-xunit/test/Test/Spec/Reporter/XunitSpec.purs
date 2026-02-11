module Test.Spec.Reporter.XunitSpec where

import Prelude

import Node.Encoding (Encoding(UTF8))
import Node.FS.Aff (readTextFile, unlink)
import Test.Spec (Spec, it, describe)
import Test.Spec.Assertions (fail)
import Test.Spec.Assertions.String (shouldContain)
import Test.Spec.Reporter.Xunit (defaultOptions, xunitReporter)
import Test.Spec.Runner (defaultConfig, runSpec')

xunitSpec :: Spec Unit
xunitSpec = do
  describe "Test" $
    describe "Spec" $
      describe "Reporter" $
        describe "Xunit" do
          it "reports success" do
            contents <- runXunit successSpec
            contents `shouldContain` "<testcase name=\"works\"></testcase>"
          it "reports failure" do
            contents <- runXunit failureSpec
            contents `shouldContain` "<testcase name=\"fails\">"
            contents `shouldContain` "Error"

  where
    successSpec = describe "a" (it "works" (pure unit))
    failureSpec = describe "a" (it "fails" (fail "OMG"))

    runXunit spec = do
      let config = defaultConfig { exit = false }
          path = "output/test.tmp.xml"
      runSpec' config [xunitReporter $ defaultOptions { outputPath = path }] spec
      contents <- readTextFile UTF8 path
      unlink path
      pure contents
