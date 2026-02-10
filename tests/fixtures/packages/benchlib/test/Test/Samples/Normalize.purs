module Test.Samples.Normalize where

import Prelude

import BenchLib (bench_, group, normalize, suite_)
import BenchLib as BenchLib
import Data.Array as Array
import Data.Foldable (all)
import Data.List (List)
import Data.List as List
import Data.List.Lazy as Lazy
import Data.List.Lazy as LazyList
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Data.Unfoldable (range)
import Effect (Effect)

main :: Effect Unit
main =
  BenchLib.runNode_ $
    suite_
      "Sample"

      [ group
          "Reverse collection"
          ( \cfg -> cfg
              { check = Just \size -> all \(input /\ output) ->
                  (input == range 0 size) && (output == Array.reverse input)

              }
          )
          [ bench_
              "List"
              (\(size :: Int) -> range 0 size)
              (\(items :: List Int) -> List.reverse items)
              # normalize List.toUnfoldable List.toUnfoldable

          , bench_
              "NonEmptyList"
              (\(size :: Int) -> range 0 size)
              (\(items :: NonEmptyList Int) -> NEL.reverse items)
              # normalize NEL.toUnfoldable NEL.toUnfoldable

          , bench_
              "Lazy List"
              (\(size :: Int) -> range 0 size)
              (\(items :: Lazy.List Int) -> LazyList.reverse items)
              # normalize LazyList.toUnfoldable LazyList.toUnfoldable

          , bench_
              "Array"
              (\(size :: Int) -> range 0 size)
              (\(items :: Array Int) -> Array.reverse items)
          ]
      ]
