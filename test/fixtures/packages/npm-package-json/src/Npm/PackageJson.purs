module Npm.PackageJson
  ( PackageJsonContent
  , PackageJson(..)
  , map
  , fromNameAndVersion
  , Person(..)
  , Author(..)
  , Bin(..)
  ) where

import Prelude
import Control.Alt ((<|>))
import Data.Argonaut
  ( class DecodeJson
  , class EncodeJson
  , Json
  , JsonDecodeError(..)
  , caseJsonObject
  , caseJsonString
  , decodeJson
  , encodeJson
  , jsonEmptyObject
  , stringify
  , (.:)
  , (.:?)
  , (:=)
  , (:=?)
  , (~>)
  , (~>?)
  )
import Data.Either (Either(..))
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Foreign.Object (Object)
import Foreign.Object as Object

type PackageJsonContent
  = { name :: String
    , version :: String
    , description :: Maybe String
    , keywords :: Maybe (Array String)
    , homepage :: Maybe String
    , author :: Maybe Author
    , contributors :: Maybe (Array Person)
    , bin :: Maybe Bin
    , private :: Maybe Boolean
    }

-- | An npm [package.json](https://docs.npmjs.com/files/package.json) file.
newtype PackageJson
  = PackageJson PackageJsonContent

map :: (PackageJsonContent -> PackageJsonContent) -> PackageJson -> PackageJson
map f (PackageJson packageJson) = PackageJson $ f packageJson

-- | Creates a new `PackageJson` from a name and a version.
fromNameAndVersion :: String -> String -> PackageJson
fromNameAndVersion name version =
  PackageJson
    { name
    , version
    , description: Nothing
    , keywords: Nothing
    , homepage: Nothing
    , author: Nothing
    , contributors: Nothing
    , bin: Nothing
    , private: Nothing
    }

derive instance genericPackageJson :: Generic PackageJson _

instance eqPackageJson :: Eq PackageJson where
  eq = genericEq

instance showPackageJson :: Show PackageJson where
  show = stringify <<< encodeJson

instance encodeJsonPackageJson :: EncodeJson PackageJson where
  encodeJson (PackageJson packageJson) = do
    "name" := packageJson.name
      ~> "version"
      := packageJson.version
      ~> "description"
      :=? packageJson.description
      ~>? "keywords"
      :=? packageJson.keywords
      ~>? "homepage"
      :=? packageJson.homepage
      ~>? "author"
      :=? packageJson.author
      ~>? "contributors"
      :=? packageJson.contributors
      ~>? "bin"
      :=? packageJson.bin
      ~>? "private"
      :=? packageJson.private
      ~>? jsonEmptyObject

instance decodeJsonPackageJson :: DecodeJson PackageJson where
  decodeJson json = do
    json' <- decodeJson json
    name <- json' .: "name"
    version <- json' .: "version"
    description <- json' .:? "description"
    keywords <- json' .:? "keywords"
    homepage <- json' .:? "homepage"
    author <- json' .:? "author"
    contributors <- json' .:? "contributors"
    bin <- json' .:? "bin"
    private <- json' .:? "private"
    pure
      $ PackageJson
          { name
          , version
          , description
          , keywords
          , homepage
          , author
          , contributors
          , bin
          , private
          }

data Person
  = Person
    { name :: String
    , email :: Maybe String
    , url :: Maybe String
    }

derive instance genericPerson :: Generic Person _

instance eqPerson :: Eq Person where
  eq = genericEq

instance encodeJsonPerson :: EncodeJson Person where
  encodeJson (Person person) = do
    "name" := person.name
      ~> "email"
      :=? person.email
      ~>? "url"
      :=? person.url
      ~>? jsonEmptyObject

instance decodeJsonPerson :: DecodeJson Person where
  decodeJson json = do
    json' <- decodeJson json
    name <- json' .: "name"
    email <- json' .:? "email"
    url <- json' .:? "url"
    pure $ Person { name, email, url }

data Author
  = AuthorString String
  | Author Person

derive instance genericAuthor :: Generic Author _

instance eqAuthor :: Eq Author where
  eq = genericEq

decodePersonFoo :: Json -> Either JsonDecodeError Person
decodePersonFoo = decodeJson

instance encodeJsonAuthor :: EncodeJson Author where
  encodeJson author = case author of
    AuthorString value -> encodeJson value
    Author value -> encodeJson value

instance decodeJsonAuthor :: DecodeJson Author where
  decodeJson json = do
    decodeAuthorString json
      <|> decodeAuthor json
    where
    decodeAuthorString :: Json -> Either JsonDecodeError Author
    decodeAuthorString json' = do
      json'' <- decodeJson json'
      pure $ AuthorString json''

    decodeAuthor :: Json -> Either JsonDecodeError Author
    decodeAuthor json' = do
      json'' <- decodeJson json'
      person <- decodeJson json''
      pure $ Author person

data Bin
  = BinPath String
  | BinPaths (Map String String)

derive instance genericBin :: Generic Bin _

instance eqBin :: Eq Bin where
  eq = genericEq

mapToObject :: Map String String -> Object Json
mapToObject =
  fromFoldable
    <<< Map.toUnfoldable
    <<< Map.mapMaybe (Just <<< encodeJson)
  where
  fromFoldable = Object.fromFoldable :: Array _ -> Object Json

mapFromObject :: Object Json -> Map String String
mapFromObject =
  Map.mapMaybe (caseJsonString Nothing Just)
    <<< Map.fromFoldable
    <<< toUnfoldable
  where
  toUnfoldable = Object.toUnfoldable :: Object Json -> Array _

instance encodeJsonBin :: EncodeJson Bin where
  encodeJson bin = case bin of
    BinPath path -> encodeJson path
    BinPaths paths -> encodeJson $ mapToObject $ paths

instance decodeJsonBin :: DecodeJson Bin where
  decodeJson json = do
    caseJsonString (Left MissingValue) (Right <<< BinPath) json
      <|> caseJsonObject (Left MissingValue) (Right <<< BinPaths <<< mapFromObject) json
