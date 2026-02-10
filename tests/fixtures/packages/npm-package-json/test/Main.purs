module Test.Main where

import Prelude
import Data.Argonaut (decodeJson, parseJson, printJsonDecodeError)
import Data.Either (either)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Npm.PackageJson (Author(..), Bin(..), Person(..), fromNameAndVersion)
import Npm.PackageJson as PackageJson
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main =
  launchAff_
    $ runSpec [ consoleReporter ] do
        describe "parse package.json" do
          describe "simple" do
            it "works" do
              let
                json =
                  """
                  {
                    "name": "my-awesome-package",
                    "version": "1.0.0",
                    "description": "This package does awesome stuff!"
                  }
                  """
              json' <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ parseJson json
              actual <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ decodeJson json'
              let
                expected =
                  fromNameAndVersion "my-awesome-package" "1.0.0"
                    # PackageJson.map _ { description = Just $ "This package does awesome stuff!" }
              actual `shouldEqual` expected
          describe "author" do
            it "works when author is a string" do
              let
                json =
                  """
                  {
                    "name": "my-awesome-package",
                    "version": "1.0.0",
                    "author": "Awesome Maintainer <awesome@example.com>"
                  }
                  """
              json' <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ parseJson json
              actual <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ decodeJson json'
              let
                expected =
                  fromNameAndVersion "my-awesome-package" "1.0.0"
                    # PackageJson.map _ { author = Just $ AuthorString "Awesome Maintainer <awesome@example.com>" }
              actual `shouldEqual` expected
            it "works when author is an object" do
              let
                json =
                  """
                  {
                    "name": "my-awesome-package",
                    "version": "1.0.0",
                    "author": {
                      "name": "Awesome Maintainer",
                      "email": "awesome@example.com"
                    }
                  }
                  """
              json' <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ parseJson json
              actual <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ decodeJson json'
              let
                expected =
                  fromNameAndVersion "my-awesome-package" "1.0.0"
                    # PackageJson.map _ { author = Just $ Author $ Person { name: "Awesome Maintainer", email: Just "awesome@example.com", url: Nothing } }
              actual `shouldEqual` expected
          describe "bin" do
            it "works when bin is a string" do
              let
                json =
                  """
                  {
                    "name": "my-awesome-package",
                    "version": "1.0.0",
                    "bin": "./cli.js"
                  }
                  """
              json' <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ parseJson json
              actual <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ decodeJson json'
              let
                expected =
                  fromNameAndVersion "my-awesome-package" "1.0.0"
                    # PackageJson.map _ { bin = Just $ BinPath "./cli.js" }
              actual `shouldEqual` expected
            it "works when bin is an object" do
              let
                json =
                  """
                  {
                    "name": "my-awesome-package",
                    "version": "1.0.0",
                    "bin": {
                      "bin-a": "./a.js",
                      "bin-b": "./b.js"
                    }
                  }
                  """
              json' <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ parseJson json
              actual <- either (liftEffect <<< throw <<< printJsonDecodeError) pure $ decodeJson json'
              let
                expected =
                  fromNameAndVersion "my-awesome-package" "1.0.0"
                    # PackageJson.map
                        _
                          { bin =
                            Just $ BinPaths $ Map.empty
                              # Map.insert "bin-a" "./a.js"
                              # Map.insert "bin-b" "./b.js"
                          }
              actual `shouldEqual` expected
