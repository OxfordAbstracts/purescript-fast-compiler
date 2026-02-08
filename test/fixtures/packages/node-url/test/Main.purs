module Test.Main where

import Prelude

import Effect (Effect)
import Node.URL as URL
import Node.URL.URLSearchParams as URL.Search
import Foreign (unsafeReadTagged)
import Data.Bifunctor (lmap)
import Control.Monad.Except (runExcept)
import Control.Monad.Error.Class (liftEither)
import Effect.Exception (error)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Map as Map
import Test.Assert (assertEqual)

main ∷ Effect Unit
main = do
  -- Simple roundtrip
  do
    let urlStr = "http://example.com/"
    url <- URL.new urlStr
    urlStr' <- URL.format url
    assertEqual { expected: urlStr, actual: urlStr' }

  -- URLSearchParams
  do
    let urlStr = "http://example.com/?k&v=a&k&v=b"
    url <- URL.new urlStr
    search <- URL.searchParams url
    keys <- URL.Search.keys search
    valuesForeign <- URL.Search.values search

    let
      getStringOrThrow =
        liftEither
          <<< lmap (error <<< show)
          <<< runExcept
          <<< unsafeReadTagged "String"

    values <- for valuesForeign getStringOrThrow

    map <- Map.fromFoldable <$> for keys \k -> do
      vs <- URL.Search.getAll k search
      pure $ Tuple k vs

    assertEqual { actual: keys, expected: [ "k", "v", "k", "v" ] }
    assertEqual { actual: values, expected: [ "", "a", "", "b" ] }
    assertEqual
      { actual: map
      , expected: Map.fromFoldable
          [ Tuple "k" [ "", "" ]
          , Tuple "v" [ "a", "b" ]
          ]
      }
