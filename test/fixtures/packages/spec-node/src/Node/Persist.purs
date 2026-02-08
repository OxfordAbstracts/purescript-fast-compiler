module Test.Spec.Runner.Node.Persist where

import Prelude

import Data.Argonaut.Core (stringifyWithIndent)
import Data.Argonaut.Decode (class DecodeJson, JsonDecodeError(..), decodeJson)
import Data.Argonaut.Decode.Decoders (decodeString)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Argonaut.Encode.Encoders (encodeString)
import Data.Argonaut.Parser (jsonParser)
import Data.DateTime.Instant as Instant
import Data.Either (hush, note)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Number as Number
import Data.String (joinWith)
import Data.Tuple.Nested ((/\))
import Effect.Aff (Aff, Milliseconds(..), catchError)
import Effect.Class (liftEffect)
import Effect.Now (now)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Test.Spec.Result as Spec
import Test.Spec.Tree (Tree(..), annotateWithPaths, parentSuiteName)

type TestFullName = String

type TestRunResults = Map.Map TestFullName
  { success :: Boolean
  , timestamp :: Timestamp
  }

newtype Timestamp = Timestamp Instant.Instant
derive instance Newtype Timestamp _

instance DecodeJson Timestamp where
  decodeJson j = j # decodeString >>= \str ->
    str # Number.fromString <#> Milliseconds >>= Instant.instant <#> wrap # note (UnexpectedValue j)

instance EncodeJson Timestamp where
  encodeJson (Timestamp t) =
    t # Instant.unInstant # unwrap # show # encodeString

persistResults :: Array (Tree String Void Spec.Result) -> Aff Unit
persistResults trees = do
  now <- Timestamp <$> liftEffect now
  let currentRun = Map.unions $ serializeRun now <$> annotateWithPaths trees

  lastRun <- lastPersistedResults

  FS.writeTextFile UTF8 persistFileName $
    stringifyWithIndent 2 $ encodeJson $ Map.union currentRun lastRun
  where
    serializeRun :: _ -> _ -> TestRunResults
    serializeRun now = case _ of
      Node _ cs ->
        Map.unions $ serializeRun now <$> cs
      Leaf _ Nothing ->
        Map.empty
      Leaf (name /\ path) (Just res) ->
        Map.singleton
          (joinWith " " $ parentSuiteName path <> [name])
          { timestamp: now
          , success: case res of
              Spec.Success _ _ -> true
              Spec.Failure _ -> false
          }

lastPersistedResults :: Aff TestRunResults
lastPersistedResults = readFile `catchError` \_ -> pure Map.empty
  where
    readFile =
      FS.readTextFile UTF8 persistFileName <#> \text ->
        text # jsonParser # hush >>= (decodeJson >>> hush) # fromMaybe Map.empty

persistFileName = ".spec-results" :: String
