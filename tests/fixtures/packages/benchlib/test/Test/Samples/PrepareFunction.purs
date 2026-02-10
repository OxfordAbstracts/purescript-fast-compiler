module Test.Samples.PrepareFunction where

import Prelude

import BenchLib (basic, bench_, group_, suite_)
import BenchLib as BenchLib
import Data.Array as Array
import Data.List (List)
import Data.List as List
import Data.Unfoldable (replicate)
import Effect (Effect)

main :: Effect Unit
main =
  BenchLib.runNode_ $
    suite_
      "Sample"

      [ group_ "Get last element"
          [ basic $ bench_
              "List"
              (\(size :: Int) -> replicate size 'x')
              (\(items :: List Char) -> List.last items)

          , basic $ bench_
              "Array"
              (\(size :: Int) -> replicate size 'x')
              (\(items :: Array Char) -> Array.last items)
          ]
      ]

