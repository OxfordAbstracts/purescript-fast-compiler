module Test.Bench (main) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List)
import Data.List as List
import Data.ResizeArray as ResizeArray
import Data.Unfoldable (range)
import Effect (Effect)
import Test.BenchLib (bench, benchGroup_, benchM, benchSuite)
import Test.BenchLib as BenchLib
import Test.BenchLib.Reporters.ChartJsHtml (reportChartJs)
import Test.MutArray as MutArray

main :: Effect Unit
main = BenchLib.run $
  let
    reporters =
      [ reportChartJs
          ( \def -> def
              { filePath = "docs/benchmarks.html"
              , lineStyles =
                  mapWithIndex (\ix val -> val { opacity = if ix == 0 then 1.0 else 0.3 }) def.lineStyles
              }
          )
      ]
  in
    benchSuite "PureScript collections CPU Benchmarks"
      ( \def -> def
          { sizes = [ 0, 20_000, 40_000, 60_000, 80_000, 100_000 ]
          , iterations = 1000
          , reporters = def.reporters <> reporters
          }
      )
      [ benchGroup_ "Delete first item"
          [ bench "ResizeArray.drop"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  , finalize = ResizeArray.toArray
                  }
              )
              (\xs -> ResizeArray.drop 1 xs)

          , bench "Array.drop"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> Array.drop 1 xs)

          , bench "List.drop"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  , finalize = List.toUnfoldable
                  }
              )
              (\xs -> List.drop 1 xs)

          , benchM "MutArray.shift"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  , finalize = MutArray.toArray
                  }
              )
              ( \xs -> do
                  MutArray.shift xs
                  pure xs
              )
          ]

      , benchGroup_ "Delete last item"
          [ bench "ResizeArray.dropEnd"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  , finalize = ResizeArray.toArray
                  }
              )
              (\xs -> ResizeArray.dropEnd 1 xs)

          , bench "Array.dropEnd"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> Array.dropEnd 1 xs)

          , bench "List.dropEnd"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  , finalize = List.toUnfoldable
                  }
              )
              (\xs -> List.dropEnd 1 xs)

          , benchM "MutArray.pop"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  , finalize = MutArray.toArray
                  }
              )
              ( \xs -> do
                  MutArray.pop xs
                  pure xs
              )
          ]

      , benchGroup_ "Add item to start"
          [ bench "ResizeArray.cons"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  , finalize = ResizeArray.toArray
                  }
              )
              (\xs -> ResizeArray.cons 0 xs)

          , bench "Array.cons"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> Array.cons 0 xs)

          , bench "List.cons"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  , finalize = List.toUnfoldable
                  }
              )
              (\xs -> List.Cons 0 xs)

          , benchM "MutArray.unshift"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  , finalize = MutArray.toArray
                  }
              )
              ( \xs -> do
                  MutArray.unshift 0 xs
                  pure xs
              )
          ]

      , benchGroup_ "Add item to end"
          [ bench "ResizeArray.snoc"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  , finalize = ResizeArray.toArray
                  }
              )
              (\xs -> ResizeArray.snoc xs 0)

          , bench "Array.snoc"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> Array.snoc xs 0)

          , bench "List.snoc"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  , finalize = List.toUnfoldable
                  }
              )
              (\xs -> List.snoc xs 0)

          , benchM "MutArray.push"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  , finalize = MutArray.toArray
                  }
              )
              ( \xs -> do
                  MutArray.push 0 xs
                  pure xs
              )
          ]

      , benchGroup_ "map over items"
          [ bench "map (ResizeArray)"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  , finalize = ResizeArray.toArray
                  }
              )
              (\xs -> map (_ + 1) xs)

          , bench "map (Array)"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> map (_ + 1) xs)

          , bench "map (List)"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  , finalize = List.toUnfoldable
                  }
              )
              (\xs -> map (_ + 1) xs)

          , benchM "MutArray.map"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  , finalize = MutArray.toArray
                  }
              )
              ( \xs -> do
                  xs' <- MutArray.map (_ + 1) xs
                  pure xs'
              )
          ]

      , benchGroup_ "foldl over items"
          [ bench "foldl (ResizeArray)"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  }
              )
              (\xs -> foldl (+) 0 xs)

          , bench "foldl (Array)"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> foldl @Array (+) 0 xs)

          , bench "foldl (List)"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> foldl @List (+) 0 xs)

          , benchM "MutArray.foldl"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  }
              )
              ( \xs -> do
                  xs' <- MutArray.foldl (+) 0 xs
                  pure xs'
              )
          ]

      , benchGroup_ "foldr over items"
          [ bench "foldr (ResizeArray)"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  }
              )
              (\xs -> foldr (+) 0 xs)

          , bench "foldr (Array)"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> foldr @Array (+) 0 xs)

          , bench "foldr (List)"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> foldr @List (+) 0 xs)

          , benchM "MutArray.foldr"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  }
              )
              ( \xs -> do
                  xs' <- MutArray.foldr (+) 0 xs
                  pure xs'
              )
          ]

      , benchGroup_ "item lookup"
          [ bench "ResizeArray.index"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  }
              )
              (\xs -> ResizeArray.index xs 0)

          , bench "Array.index"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> Array.index xs 0)

          , bench "List.index"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> List.index xs 0)

          , benchM "MutArray.lookup"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  }
              )
              ( \xs -> do
                  xs' <- MutArray.lookup 0 xs
                  pure xs'
              )
          ]
      , benchGroup_ "size"
          [ bench "ResizeArray.length"
              ( \def -> def
                  { prepare = \size -> ResizeArray.fromArray $ range 1 size
                  }
              )
              (\xs -> ResizeArray.length xs)

          , bench "Array.length"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> Array.length xs)

          , bench "List.length"
              ( \def -> def
                  { prepare = \size -> range 1 size
                  }
              )
              (\xs -> List.length xs)

          , benchM "MutArray.length"
              ( \def -> def
                  { prepare = \size -> MutArray.fromArray $ range 1 size
                  }
              )
              ( \xs -> do
                  pure $ MutArray.length xs
              )
          ]
      ]

