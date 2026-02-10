-- | DataViz.Layout.Chord.Layout
-- |
-- | Pure PureScript implementation of the chord layout algorithm.
-- |
-- | The algorithm:
-- | 1. Compute row sums to get total value for each group
-- | 2. Compute the grand total of all values
-- | 3. Assign angular extent to each group proportional to its value
-- | 4. For each non-zero matrix[i][j], create a chord connecting groups
-- | 5. Track angular position within each group for ribbon placement
module DataViz.Layout.Chord.Layout
  ( layout
  , layoutWithConfig
  ) where

import Prelude

import Data.Array (concat, foldl, length, mapWithIndex, zip, (!!))
import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (fromMaybe)
import Data.Number (pi)
import Data.Tuple (Tuple(..))
import DataViz.Layout.Chord.Types (ChordGroup, Chord, ChordLayout, LayoutConfig, defaultConfig)

-- | Layout a chord diagram with default configuration
layout :: Array (Array Number) -> ChordLayout
layout = layoutWithConfig defaultConfig

-- | Layout a chord diagram with custom configuration
layoutWithConfig :: LayoutConfig -> Array (Array Number) -> ChordLayout
layoutWithConfig config matrix =
  let
    n = length matrix

    -- Step 1: Compute row sums (total outgoing from each node)
    rowSums = map (foldl (+) 0.0) matrix

    -- Step 2: Grand total
    grandTotal = foldl (+) 0.0 rowSums

    -- Avoid division by zero
    safeTotal = if grandTotal == 0.0 then 1.0 else grandTotal

    -- Step 3: Compute total angular extent available (minus padding)
    totalPadding = config.padAngle * toNumber n
    availableAngle = (config.endAngle - config.startAngle) - totalPadding

    -- Step 4: Compute group angles
    -- Each group gets angle proportional to its row sum
    groupAngles = computeGroupAngles config.startAngle config.padAngle availableAngle safeTotal rowSums

    -- Step 5: Build groups
    groups = mapWithIndex (\i (Tuple startAngle endAngle) ->
      { index: i
      , startAngle
      , endAngle
      , value: fromMaybe 0.0 (rowSums !! i)
      }) groupAngles

    -- Step 6: Build chords
    -- For each group, track current angle position for ribbon placement
    chords = buildChords matrix groups availableAngle safeTotal
  in
    { groups, chords }

-- | Compute start and end angles for each group
computeGroupAngles
  :: Number          -- Start angle
  -> Number          -- Pad angle between groups
  -> Number          -- Total available angle (after padding)
  -> Number          -- Grand total value
  -> Array Number    -- Row sums
  -> Array (Tuple Number Number)
computeGroupAngles startAngle padAngle availableAngle grandTotal rowSums =
  let
    -- Accumulate angles
    accumulate :: { currentAngle :: Number, result :: Array (Tuple Number Number) }
               -> Number
               -> { currentAngle :: Number, result :: Array (Tuple Number Number) }
    accumulate { currentAngle, result } value =
      let
        -- Angular extent for this group
        extent = (value / grandTotal) * availableAngle
        groupStart = currentAngle
        groupEnd = currentAngle + extent
        nextAngle = groupEnd + padAngle
      in
        { currentAngle: nextAngle
        , result: result `Array.snoc` Tuple groupStart groupEnd
        }

    initial = { currentAngle: startAngle, result: [] }
  in
    (foldl accumulate initial rowSums).result

-- | Build all chords from the matrix
-- | For each non-zero entry matrix[i][j], create a chord from group i to group j
buildChords
  :: Array (Array Number)  -- Matrix
  -> Array ChordGroup      -- Groups with their angles
  -> Number                -- Available angle
  -> Number                -- Grand total
  -> Array Chord
buildChords matrix groups availableAngle grandTotal =
  let
    n = length groups

    -- For each group, track how much angle has been consumed by chords
    -- We need to track this per-group as we iterate through the matrix
    -- Start with the group's startAngle for each
    initialOffsets = map _.startAngle groups

    -- Build chords row by row
    -- For row i, we create chords for all non-zero values in that row
    buildRow :: { offsets :: Array Number, chords :: Array Chord }
             -> Tuple Int (Array Number)
             -> { offsets :: Array Number, chords :: Array Chord }
    buildRow state (Tuple rowIdx row) =
      let
        sourceGroup = fromMaybe emptyGroup (groups !! rowIdx)

        -- Build chords for this row
        buildCell :: { offset :: Number, chords :: Array Chord }
                  -> Tuple Int Number
                  -> { offset :: Number, chords :: Array Chord }
        buildCell cellState (Tuple colIdx value) =
          if value <= 0.0 then cellState
          else
            let
              targetGroup = fromMaybe emptyGroup (groups !! colIdx)

              -- Compute angular extent for this chord on the source side
              -- Proportional to value relative to source group's total
              sourceExtent = if sourceGroup.value == 0.0
                             then 0.0
                             else (value / sourceGroup.value) * (sourceGroup.endAngle - sourceGroup.startAngle)

              -- The chord's source segment
              sourceStart = cellState.offset
              sourceEnd = sourceStart + sourceExtent

              -- For target, we need to find where to place it
              -- This requires tracking target offsets separately
              -- For now, compute based on target group's value proportion
              targetValue = fromMaybe 0.0 ((matrix !! colIdx) >>= (_ !! rowIdx))
              targetExtent = if targetGroup.value == 0.0
                             then 0.0
                             else (targetValue / targetGroup.value) * (targetGroup.endAngle - targetGroup.startAngle)

              -- Simplified: place target at position based on matrix symmetry
              -- In a proper implementation, we'd track target offsets too
              targetStart = targetGroup.startAngle +
                (value / (if targetGroup.value == 0.0 then 1.0 else targetGroup.value)) *
                (targetGroup.endAngle - targetGroup.startAngle) * 0.5
              targetEnd = targetStart + targetExtent

              chord :: Chord
              chord =
                { source:
                    { index: rowIdx
                    , startAngle: sourceStart
                    , endAngle: sourceEnd
                    , value
                    }
                , target:
                    { index: colIdx
                    , startAngle: targetStart
                    , endAngle: min targetEnd targetGroup.endAngle
                    , value: targetValue
                    }
                }
            in
              { offset: sourceEnd
              , chords: cellState.chords `Array.snoc` chord
              }

        -- Process all cells in this row
        rowResult = foldl buildCell
          { offset: sourceGroup.startAngle, chords: state.chords }
          (mapWithIndex Tuple row)
      in
        { offsets: state.offsets
        , chords: rowResult.chords
        }

    -- Process all rows
    result = foldl buildRow
      { offsets: initialOffsets, chords: [] }
      (mapWithIndex Tuple matrix)
  in
    result.chords

-- | Empty group for fallback
emptyGroup :: ChordGroup
emptyGroup =
  { index: 0
  , startAngle: 0.0
  , endAngle: 0.0
  , value: 0.0
  }
