module Test.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)
import Web.URL as URL
import Web.URL.URLSearchParams as USP

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  describe "URL" do

    describe "fromAbsolute" do
      it "returns a URL when given an absolute URL" do
        (show <$> URL.fromAbsolute "http://www.remakingthe.world")
          `shouldEqual` Just "http://www.remakingthe.world/"
      it "returns Nothing when given an invalid URL" do
        URL.fromAbsolute "this.is.not.valid"
          `shouldEqual` Nothing

    describe "fromRelative" do
      it "returns a URL when given a relative and base URL" do
        let u = URL.fromRelative "/matthias/" "http://www.remakingthe.world"
        (show <$> u) `shouldEqual` Just "http://www.remakingthe.world/matthias/"
      it "returns Nothing when given an invalid URL" do
        URL.fromRelative "/matthias/" "this.is.not.valid"
          `shouldEqual` Nothing

    describe "hash" do
      it "returns a hash for a URL" do
        (URL.hash $ URL.unsafeFromAbsolute "http://www.remakingthe.world/matthias/#fr")
          `shouldEqual` "#fr"
      it "returns an empty string when the URL has no hash" do
        (URL.hash $ URL.unsafeFromAbsolute "http://www.remakingthe.world/matthias/")
          `shouldEqual` ""

    describe "hosts" do
      it "returns a hostname for a URL" do
        (URL.host $ URL.unsafeFromAbsolute "http://www.remakingthe.world/matthias/")
          `shouldEqual` "www.remakingthe.world"
      it "returns host with port for a URL" do
        (URL.host $ URL.unsafeFromAbsolute "http://www.remakingthe.world:8000/")
          `shouldEqual` "www.remakingthe.world:8000"

    describe "hostname" do
      it "returns the hostname for a URL" do
        (URL.host $ URL.unsafeFromAbsolute "http://www.remakingthe.world/matthias/")
          `shouldEqual` "www.remakingthe.world"
      it "returns the hostname without port for a URL" do
        (URL.hostname $ URL.unsafeFromAbsolute "http://www.remakingthe.world:8000/")
          `shouldEqual` "www.remakingthe.world"

    describe "href" do
      it "returns the href (complete string) for a URL" do
        (URL.href $ URL.unsafeFromAbsolute "http://www.remakingthe.world/matthias/#fr")
          `shouldEqual` "http://www.remakingthe.world/matthias/#fr"

    describe "origin" do
      it "returns the origin (scheme, domain & port) for a URL" do
        (URL.origin $ URL.unsafeFromAbsolute "http://www.remakingthe.world/matthias/#fr")
          `shouldEqual` "http://www.remakingthe.world"
      it "returns the hostname without port for a URL if port is default port of scheme" do
        (URL.origin $ URL.unsafeFromAbsolute "https://www.remakingthe.world:443/")
          `shouldEqual` "https://www.remakingthe.world"

    describe "password" do
      it "returns the password for the URL" do
        (URL.password $ URL.unsafeFromAbsolute "http://matthias:ensure@www.remakingthe.world/")
          `shouldEqual` "ensure"
      it "returns an empty string if the URL has no password" do
        (URL.password $ URL.unsafeFromAbsolute "http://matthias@www.remakingthe.world/")
          `shouldEqual` ""

    describe "pathname" do
      it "returns the pathname of the URL" do
        (URL.pathname $ URL.unsafeFromAbsolute "http://www.example.com/this/is/the/path/")
          `shouldEqual` "/this/is/the/path/"
      it "returns '/' if the URL has no pathname" do
        (URL.pathname $ URL.unsafeFromAbsolute "http://example.com")
          `shouldEqual` "/"

    describe "port" do
      it "returns the port of the URL" do
        (URL.port $ URL.unsafeFromAbsolute "http://www.example.com:8000/")
          `shouldEqual` "8000"
      it "returns an empty string if the URL has no port" do
        (URL.port $ URL.unsafeFromAbsolute "http://www.example.com/")
          `shouldEqual` ""

    describe "protocol" do
      it "returns the protocol of the URL" do
        (URL.protocol $ URL.unsafeFromAbsolute "https://www.example.com/")
          `shouldEqual` "https:"

    describe "search" do
      it "returns the query string of the URL" do
        (URL.search $ URL.unsafeFromAbsolute "https://www.example.com/?foo=1")
          `shouldEqual` "?foo=1"
      it "returns an empty string if the URL has no query string" do
        (URL.search $ URL.unsafeFromAbsolute "http://www.example.com/")
          `shouldEqual` ""

    describe "searchParams" do
      it "returns a URLSearchParams from the URL" do
        (show $ URL.searchParams $ URL.unsafeFromAbsolute "https://www.example.com/?foo=1")
          `shouldEqual` "foo=1"
      it "returns an empty URLSearchParams if the URL has no query string" do
        (show $ URL.searchParams $ URL.unsafeFromAbsolute "http://www.example.com/")
          `shouldEqual` ""

    describe "username" do
      it "returns the username for the URL" do
        (URL.username $ URL.unsafeFromAbsolute "http://matthias:ensure@www.remakingthe.world/")
          `shouldEqual` "matthias"
      it "returns an empty string if the URL has no username" do
        (URL.username $ URL.unsafeFromAbsolute "http://www.remakingthe.world/")
          `shouldEqual` ""

  describe "URLSearchParams" do
    describe "fromString" do
      it "returns a URLSearhParams for form encoded string" do
        (show $ USP.fromString "foo=1&bar=2")
          `shouldEqual` "foo=1&bar=2"

    describe "append" do
      it "appends the parameters to the URLSearchParams" do
        (show $USP.append "baz" "3" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` "foo=1&bar=2&baz=3"
      it "keeps the original URLSearchParams unmodified" do
        let p = USP.fromString "foo=1&bar=2"
        let _ = USP.append "baz" "3"
        show p `shouldEqual` "foo=1&bar=2"

    describe "delete" do
      it "deletes the given key from the URLSearchParams" do
        (show $ USP.delete "bar" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` "foo=1"
      it "keeps the original URLSearchParams unmodified" do
        let p = USP.fromString "foo=1&bar=2"
        let _ = USP.delete "baz"
        show p `shouldEqual` "foo=1&bar=2"

    describe "entries" do
      it "returns an Array of Tuples for a URLSearchParams" do
        (USP.entries $ USP.fromString "foo=1&bar=2")
          `shouldEqual` [Tuple "foo" "1", Tuple "bar" "2"]
      it "returns an empty Array for an empty URLSearchParams" do
        (USP.entries $ USP.fromString "")
          `shouldEqual` []

    describe "get" do
      it "returns an existing key for a URLSearchParams" do
        (USP.get "foo" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` Just "1"
      it "returns Nothing if the key is missing" do
        (USP.get "baz" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` Nothing

    describe "getAll" do
      it "returns an Array for a URLSearchParams" do
        (USP.getAll "foo" $ USP.fromString "foo=1&foo=there_is_more_foo")
          `shouldEqual` ["1", "there_is_more_foo"]
      it "returns an empty Array if the key is missing" do
        (USP.getAll "baz" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` []

    describe "has" do
      it "returns True if the key exists in the URLSearchParams" do
        (USP.has "foo" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` true
      it "returns False if the key exists in the URLSearchParams" do
        (USP.has "baz" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` false

    describe "keys" do
      it "returns an Array of keys for the given URLSearchParams" do
        (USP.keys $ USP.fromString "foo=1&bar=2")
          `shouldEqual` ["foo", "bar"]
      it "returns an empty Array if the URLSearchParams is empty" do
        (USP.keys $ USP.fromString "")
          `shouldEqual` []

    describe "set" do
      it "setting an existing key updates it in the URLSearchParams" do
        (show $ USP.set "foo" "3" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` "foo=3&bar=2"
      it "setting a non existing key adds it to the URLSearchParams" do
        (show $ USP.set "baz" "3" $ USP.fromString "foo=1&bar=2")
          `shouldEqual` "foo=1&bar=2&baz=3"
      it "keeps the original URLSearchParams unmodified" do
        let p = USP.fromString "foo=1&bar=2"
        let _ = USP.set "baz" "3"
        show p `shouldEqual` "foo=1&bar=2"

    describe "sort" do
      it "sorts the key/values in the URLSearchParams" do
        (show $ USP.sort $ USP.fromString "foo=1&bar=2")
          `shouldEqual` "bar=2&foo=1"
      it "keeps the original URLSearchParams unmodified" do
        let p = USP.fromString "foo=1&bar=2"
        let _ = USP.sort p
        show p `shouldEqual` "foo=1&bar=2"

    describe "toString" do
      it "toString <<< fromString ~ identity" do
        (USP.toString $ USP.fromString "foo=1&bar=2")
          `shouldEqual` "foo=1&bar=2"
      it "toString <<< fromString ~ identity (empty string)" do
        (USP.toString $ USP.fromString "")
          `shouldEqual` ""

    describe "values" do
      it "returns an Array of values for the given URLSearchParams" do
        (USP.values $ USP.fromString "foo=1&bar=2")
          `shouldEqual` ["1", "2"]
      it "returns an empty Array if the URLSearchParams is empty" do
        (USP.values $ USP.fromString "")
          `shouldEqual` []
