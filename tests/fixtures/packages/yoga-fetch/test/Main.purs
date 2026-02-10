module Test.Main where

import Prelude

import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Either (Either(..), isRight)
import Data.String (null)
import Effect (Effect)
import Effect.Aff (attempt, launchAff_)
import Foreign.Object as Object
import Yoga.Fetch as Fetch
import Yoga.Fetch.Impl.Node (nodeFetch)
import Test.Spec (describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldContain)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

fetch ∷ Fetch.Fetch
fetch = Fetch.fetch nodeFetch

main ∷ Effect Unit
main = launchAff_ $ runSpec [ consoleReporter ] do
  describe "purescript-yoga-fetch" do
    it "get works and gets a body" do
      _response ← attempt $ fetch (Fetch.URL "https://www.google.com")
        Fetch.defaultFetchOptions
      case _response of
        Left e → do
          fail $ "failed with " <> show e
        Right response → do
          stuff ← Fetch.text response
          let code = Fetch.statusCode response
          code `shouldEqual` 200
          null stuff `shouldEqual` false
          let headers = Fetch.headers response
          Object.keys headers `shouldContain` "content-type"
          Object.keys headers `shouldContain` "content-encoding"

    it "get works and gets a body" do
      _response ← attempt $ fetch (Fetch.URL "https://www.google.com")
        Fetch.defaultFetchOptions
      case _response of
        Left e → do
          fail $ "failed with " <> show e
        Right response → do
          arrayBuffer ← Fetch.arrayBuffer response
          let code = Fetch.statusCode response
          code `shouldEqual` 200
          (byteLength arrayBuffer > 0) `shouldEqual` true

    it "gets an url" do
      _response ← attempt $ fetch (Fetch.URL "https://www.google.com")
        Fetch.defaultFetchOptions
      case _response of
        Left e → do
          fail $ "failed with " <> show e
        Right response → do
          let url = Fetch.url response
          url `shouldEqual` (Fetch.URL "https://www.google.com/")

    it "post works" do
      let
        opts =
          { method: Fetch.postMethod
          , body: "{}"
          , headers: Fetch.makeHeaders { "Content-Type": "application/json" }
          }
      result ← attempt $ fetch (Fetch.URL "https://www.google.com") opts
      isRight result `shouldEqual` true
    it "put works" do
      let opts = { method: Fetch.putMethod }
      result ← attempt $ fetch (Fetch.URL "https://www.google.com") opts
      isRight result `shouldEqual` true
    it "patch works" do
      let opts = { method: Fetch.patchMethod }
      result ← attempt $ fetch (Fetch.URL "https://www.google.com") opts
      isRight result `shouldEqual` true
    it "delete works" do
      let opts = { method: Fetch.deleteMethod }
      result ← attempt $ fetch (Fetch.URL "https://www.google.com") opts
      isRight result `shouldEqual` true

foreign import byteLength ∷ ArrayBuffer → Int
