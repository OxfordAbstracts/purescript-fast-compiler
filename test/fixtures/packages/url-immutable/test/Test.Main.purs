module Test.Main where

import Prelude hiding ((/), (#))

import Control.Monad.Error.Class (liftMaybe, throwError)
import Data.Either (Either(..), isRight)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (for_)
import Data.Tuple.Nested ((/\))
import Data.URL (Path(..), URL, pathOrURLFromString, resolveString, toString, (#), (&), (/), (?))
import Data.URL as URL
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Exception (error)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = launchAff_ $ runSpec [ consoleReporter ] do
  describe "URL" do
    let
      fromString_ :: String -> Aff URL
      fromString_ u = liftMaybe (error $ "parsing failed: " <> u) $ URL.fromString u

    describe "fromString" do
      it "returns Just on valid URL" do
        void $ fromString_ "https://google.com"
        void $ fromString_ "http://localhost?foo=bar&foo&foo&bar=baz"
        void $ fromString_ "postgresql://user:pass@1.2.3.4:5432/dbname"
      it "returns Nothing on invalid URL" do
        let
          case_ :: String -> Aff Unit
          case_ u = maybe (pure unit) (const $ throwError $ error $ "parsing erroneously succeeded: " <> u) $ URL.fromString u
        case_ "google.com"
        case_ "localhost"
        case_ "http://?feai#dfkvsj"

    describe "pathOrURLFromString" do
      it "returns Right on valid URL" do
        isRight (pathOrURLFromString "https://google.com") `shouldEqual` true
        isRight (pathOrURLFromString "http://localhost?foo=bar&foo&foo&bar=baz") `shouldEqual` true
        isRight (pathOrURLFromString "postgresql://user:pass@1.2.3.4:5432/dbname") `shouldEqual` true
      it "returns Left on anything else" do
        (pathOrURLFromString "/foo") `shouldEqual` (Left $ PathAbsolute [ "foo" ])
        (pathOrURLFromString "./../../foo") `shouldEqual` (Left $ PathRelative [ ".", "..", "..", "foo" ])
        (pathOrURLFromString "foo") `shouldEqual` (Left $ PathRelative [ "foo" ])
        (pathOrURLFromString "") `shouldEqual` (Left PathEmpty)
        (pathOrURLFromString "941389dfajifdjiao34910fd#$@?!") `shouldEqual` (Left $ PathRelative [ "941389dfajifdjiao34910fd#$@?!" ])

    describe "resolveString" do
      it "works" do
        (shouldEqual "https://google.com/foo")
          =<< toString
            <$> resolveString "/foo"
            <$> fromString_ "https://google.com/a/b/c/d/e"
        (shouldEqual "https://google.com/foo/bar/baz/a")
          =<< toString
            <$> resolveString "./a"
            <$> fromString_ "https://google.com/foo/bar/baz"
        (shouldEqual "https://google.com/foo/a")
          =<< toString
            <$> resolveString "../../a"
            <$> fromString_ "https://google.com/foo/bar/baz"
        (shouldEqual "https://cheese.com/foo/bar")
          =<< toString
            <$> resolveString "https://cheese.com/foo/bar"
            <$> fromString_ "https://google.com/foo/bar/baz"

    describe "toString" do
      it "stringifies" do
        let
          case_ :: String -> Aff Unit
          case_ u = do
            url <- fromString_ u
            URL.toString url `shouldEqual` u
        case_ "https://google.com/"
        case_ "http://localhost/?foo=bar&foo&foo&bar=baz"
        case_ "postgresql://user:pass@1.2.3.4:5432/dbname"

    describe "get" do
      describe "path" do
        let
          cases =
            [ "https://google.com/foo" /\ URL.PathAbsolute [ "foo" ]
            , "http://localhost/bar?foo=bar" /\ URL.PathAbsolute [ "bar" ]
            , "http://1.1.1.1:4142/asdf/foo/bingus#asdf" /\ URL.PathAbsolute [ "asdf", "foo", "bingus" ]
            , "https://google.com/" /\ URL.PathEmpty
            , "http://localhost/?foo=bar" /\ URL.PathEmpty
            , "http://1.1.1.1:4142/#asdf" /\ URL.PathEmpty
            ]
        for_ cases \(u /\ expect) -> it (u <> " -> " <> show expect) do
          url <- fromString_ u
          URL.path url `shouldEqual` expect

      describe "query" do
        let
          cases =
            [ "https://google.com       " /\ Map.empty
            , "https://google.com?k     " /\ Map.singleton "k" [ "" ]
            , "https://google.com?k&k&k " /\ Map.singleton "k" [ "", "", "" ]
            , "https://localhost/foo?q#a" /\ Map.singleton "q" [ "" ]
            , "https://a?a=a&b=b&b=c    " /\ Map.fromFoldable [ "a" /\ [ "a" ], "b" /\ [ "b", "c" ] ]
            ]
        for_ cases \(u /\ expect) -> it (u <> " -> " <> show expect) do
          url <- fromString_ u
          let qs = URL.query url
          qs `shouldEqual` expect
      describe "host" do
        let
          cases =
            [ "https://google.com  " /\ "google.com"
            , "https://localhost   " /\ "localhost"
            , "https://1.1.1.1     " /\ "1.1.1.1"
            , "https://1.1.1.1:5432" /\ "1.1.1.1"
            ]
        for_ cases \(u /\ expect) -> it (u <> " -> " <> expect) do
          url <- fromString_ u
          URL.host url `shouldEqual` expect
      describe "port" do
        let
          cases =
            [ "https://google.com  " /\ Nothing
            , "https://localhost   " /\ Nothing
            , "https://1.1.1.1     " /\ Nothing
            , "https://1.1.1.1:5432" /\ Just 5432
            ]
        for_ cases \(u /\ expect) -> it (u <> " -> " <> show expect) do
          url <- fromString_ u
          URL.port url `shouldEqual` expect
      describe "hash" do
        let
          cases =
            [ "https://google.com    " /\ Nothing
            , "https://google.com#foo" /\ Just "foo"
            , "https://localhost     " /\ Nothing
            , "https://1.1.1.1:5432  " /\ Nothing
            ]
        for_ cases \(u /\ expect) -> it (u <> " -> " <> show expect) do
          url <- fromString_ u
          URL.hash url `shouldEqual` expect
      describe "username" do
        let
          cases =
            [ "https://google.com       " /\ Nothing
            , "https://google.com#foo   " /\ Nothing
            , "https://:bar@google.com  " /\ Nothing
            , "https://foo@localhost    " /\ Just "foo"
            , "https://foo:bar@localhost" /\ Just "foo"
            ]
        for_ cases \(u /\ expect) -> it (u <> " -> " <> show expect) do
          url <- fromString_ u
          URL.username url `shouldEqual` expect
      describe "password" do
        let
          cases =
            [ "https://google.com       " /\ Nothing
            , "https://google.com#foo   " /\ Nothing
            , "https://:bar@google.com  " /\ Just "bar"
            , "https://foo@localhost    " /\ Nothing
            , "https://foo:bar@localhost" /\ Just "bar"
            ]
        for_ cases \(u /\ expect) ->
          it (u <> " -> " <> show expect) do
            url <- fromString_ u
            URL.password url `shouldEqual` expect
      describe "protocol" do
        let
          cases =
            [ "https://google.com    " /\ "https"
            , "https://google.com#foo" /\ "https"
            , "http://:bar@google.com" /\ "http"
            , "http://1.1.1.1        " /\ "http"
            , "coap://1.1.1.1        " /\ "coap"
            , "ssh://1.1.1.1         " /\ "ssh"
            , "data:text/plain,foo   " /\ "data"
            ]
        for_ cases \(u /\ expect) ->
          it (u <> " -> " <> expect) do
            url <- fromString_ u
            URL.protocol url `shouldEqual` expect
    describe "set" do
      it "resolve" do
        u <- fromString_ "https://google.com/search"
        let
          rel = URL.resolve (URL.PathRelative [ "foo", "bar" ]) u
          abs = URL.resolve (URL.PathAbsolute [ "foo", "bar" ]) u
        URL.toString rel `shouldEqual` "https://google.com/search/foo/bar"
        URL.toString abs `shouldEqual` "https://google.com/foo/bar"
      it "setQuery" do
        u <- fromString_ "https://google.com?k"
        let
          u' = URL.setQuery (Map.fromFoldable [ "a" /\ [ "b", "" ] ]) u
        URL.toString u' `shouldEqual` "https://google.com/?a=b&a="
      it "setters do not mutate original url" do
        url <- fromString_ "https://google.com/"
        let
          foo = URL.setHost "foo.com" url
          fooBuilt =
            URL.setUsername "user"
              $ URL.setPassword "pass"
              $ URL.setProtocol "https"
              $ URL.setPort 1234
              $ foo / "cheese" / "brie" ? "k" /\ "v" & "k" # "foo"
        URL.toString url `shouldEqual` "https://google.com/"
        URL.toString fooBuilt `shouldEqual` "https://user:pass@foo.com:1234/cheese/brie?k=&k=v#foo"
