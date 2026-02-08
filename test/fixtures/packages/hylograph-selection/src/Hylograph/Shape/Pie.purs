-- | Pure PureScript Pie Layout
-- |
-- | Computes start/end angles for pie and donut charts.
-- | No D3 dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hylograph.Shape.Pie (pie, PieSlice)
-- | import Hylograph.Shape.Arc (arcPath)
-- |
-- | let data = [30.0, 50.0, 20.0]
-- | let slices = pie identity data
-- |
-- | -- Each slice has { value, startAngle, endAngle, index, data }
-- | let paths = map (\s -> arcPath { innerRadius: 0.0, outerRadius: 100.0 } s) slices
-- | ```
module Hylograph.Shape.Pie
  ( -- * Types
    PieSlice
  , PieConfig
    -- * Pie Layout
  , pie
  , pieWithConfig
  , defaultPieConfig
    -- * Utilities
  , sortByValue
  , sortByValueDesc
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (sum)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Number (pi)

-- | Configuration for pie layout
type PieConfig =
  { startAngle :: Number     -- ^ Starting angle (default 0)
  , endAngle :: Number       -- ^ Ending angle (default 2π)
  , padAngle :: Number       -- ^ Padding between slices in radians (default 0)
  , sort :: forall a. Array a -> Array a  -- ^ Sort function (default: no sort)
  }

-- | A slice of the pie with computed angles
type PieSlice a =
  { value :: Number        -- ^ The numeric value
  , startAngle :: Number   -- ^ Start angle in radians
  , endAngle :: Number     -- ^ End angle in radians
  , padAngle :: Number     -- ^ Padding angle
  , index :: Int           -- ^ Original index in data array
  , data :: a              -- ^ Original data item
  }

-- | Default pie configuration
-- | Full circle, no padding, no sorting
defaultPieConfig :: PieConfig
defaultPieConfig =
  { startAngle: 0.0
  , endAngle: 2.0 * pi
  , padAngle: 0.0
  , sort: identity
  }

-- | Compute pie slices from data using a value accessor
-- |
-- | ```purescript
-- | -- Simple array of numbers
-- | pie identity [10.0, 20.0, 30.0]
-- |
-- | -- Array of records
-- | pie _.sales [{ name: "A", sales: 100.0 }, { name: "B", sales: 200.0 }]
-- | ```
pie :: forall a. (a -> Number) -> Array a -> Array (PieSlice a)
pie = pieWithConfig defaultPieConfig

-- | Compute pie slices with custom configuration
pieWithConfig :: forall a. PieConfig -> (a -> Number) -> Array a -> Array (PieSlice a)
pieWithConfig config getValue data_ =
  let
    -- Sort data if configured
    sortedData = config.sort data_

    -- Create indexed data to preserve original indices
    indexedData = Array.mapWithIndex (\i d -> { index: i, data: d, value: getValue d }) sortedData

    -- Calculate total
    total = sum (map _.value indexedData)

    -- Available arc span (minus padding)
    n = Array.length indexedData
    totalPadding = config.padAngle * (if n > 1 then toNumber (n - 1) else 0.0)
    availableArc = config.endAngle - config.startAngle - totalPadding

    -- Scale factor: radians per unit value
    scale = if total > 0.0 then availableArc / total else 0.0

    -- Build slices with cumulative angles
    buildSlices :: Number -> Array { index :: Int, data :: a, value :: Number } -> Array (PieSlice a)
    buildSlices _ items | Array.null items = []
    buildSlices currentAngle items =
      case Array.uncons items of
        Nothing -> []
        Just { head: item, tail: rest } ->
          let
            arcLength = item.value * scale
            slice =
              { value: item.value
              , startAngle: currentAngle
              , endAngle: currentAngle + arcLength
              , padAngle: config.padAngle
              , index: item.index
              , data: item.data
              }
            nextAngle = currentAngle + arcLength + (if Array.null rest then 0.0 else config.padAngle)
          in
            Array.cons slice (buildSlices nextAngle rest)

  in
    buildSlices config.startAngle indexedData

-- | Sort comparator: by value ascending
sortByValue :: forall a. Ord a => Array a -> Array a
sortByValue = Array.sort

-- | Sort comparator: by value descending
sortByValueDesc :: forall a. Ord a => Array a -> Array a
sortByValueDesc = Array.reverse <<< Array.sort
