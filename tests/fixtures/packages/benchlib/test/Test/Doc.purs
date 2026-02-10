module Test.Doc where

import Prelude

import BenchLib (Bench, Group, Size, Suite)
import BenchLib as BL
import Data.Array (all)
import Data.Array as Array
import Data.List.Lazy (List)
import Data.List.Lazy as List
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as String
import Data.Tuple.Nested ((/\))

prepareCharArray :: Size -> Array Char
prepareCharArray size = Array.replicate size 'x'

prepareCharList :: Size -> List Char
prepareCharList size = List.replicate size 'x'

prepareString :: Size -> String
prepareString size = String.fromCharArray (Array.replicate size 'x')

bench1 :: Bench (Array Char) Int
bench1 = BL.bench_ "Length of Array of Char"
  prepareCharArray
  Array.length

bench2 :: Bench (List Char) Int
bench2 = BL.bench_ "Length of List of Char"
  prepareCharList
  List.length

bench3 :: Bench String Int
bench3 = BL.bench_ "Length of String"
  prepareString
  String.length

benchBasic1 :: Bench Unit Unit
benchBasic1 = BL.basic bench1

benchBasic2 :: Bench Unit Unit
benchBasic2 = BL.basic bench2

benchBasic3 :: Bench Unit Unit
benchBasic3 = BL.basic bench3

groupBasic :: Group
groupBasic = BL.group_
  "Length operations"
  [ benchBasic1
  , benchBasic2
  , benchBasic3
  ]

groupBasic' :: Group
groupBasic' = BL.group
  "Length operations"
  (\opts -> opts)
  [ benchBasic1
  , benchBasic2
  , benchBasic3
  ]

benchNormalized1 :: Bench (Array Char) Int
benchNormalized1 = bench1

benchNormalized2 :: Bench (Array Char) Int
benchNormalized2 = BL.normalizeInput List.toUnfoldable bench2

benchNormalized3 :: Bench (Array Char) Int
benchNormalized3 = BL.normalizeInput String.toCharArray bench3

groupNormalized :: Group
groupNormalized = BL.group_
  "Length of Char"
  [ benchNormalized1
  , benchNormalized2
  , benchNormalized3
  ]

suite1 ∷ Suite
suite1 = BL.suite_ "My Benchmarks"
  [ groupNormalized
  ]

suite2 ∷ Suite
suite2 =
  BL.suite_
    "My Benchmarks"
    [ BL.group
        "Length operations"
        ( \opts -> opts
            { sizes = [ 1, 10, 100, 1000 ]
            , iterations = 1000

            , check = Just \size -> all \(input /\ output) ->
                (input == Array.replicate size 'x') && (output == Array.length input)

            }
        )
        [ BL.bench_
            "Length of Array of Char"
            (\size -> Array.replicate size 'x')
            Array.length

        , BL.normalizeInput List.toUnfoldable $ BL.bench_
            "Length of List of Char"
            (\size -> List.replicate size 'x')
            List.length

        , BL.normalizeInput String.toCharArray $ BL.bench_
            "Length of String"
            (\size -> String.fromCharArray (Array.replicate size 'x'))
            String.length
        ]
    ]