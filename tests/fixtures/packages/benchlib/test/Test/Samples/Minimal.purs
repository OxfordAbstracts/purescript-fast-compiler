--- Header

module Test.Samples.Minimal where

import Prelude

import BenchLib (basic, group_, suite_, bench_)
import BenchLib as BenchLib
import Data.Array as Array
import Data.List.Lazy as LazyList
import Effect (Effect)

--- Main

main :: Effect Unit
main = BenchLib.runNode_ $
  suite_
    "Minimal Example"
    [ group_ "Replicate Functions"
        [ basic $ bench_
            "Array"
            identity
            (\size -> Array.replicate size 'x')

        , basic $ bench_
            "Lazy List"
            identity
            (\size -> LazyList.replicate size 'x')
        ]
    ]

