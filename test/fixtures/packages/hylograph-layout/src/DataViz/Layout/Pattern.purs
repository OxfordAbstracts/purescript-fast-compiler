-- | Geometric Layout Patterns
-- |
-- | Simple, deterministic layout functions for positioning N items within a viewport.
-- | Each function handles all the tedious calculations (aspect ratio, spacing, centering)
-- | and returns an array of points ready to zip with your data.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import DataViz.Layout.Pattern (grid, phyllotaxis)
-- | import DataViz.Layout.Pattern.Types (viewportWithPadding)
-- |
-- | -- Layout 100 items in a grid with 20px padding
-- | let vp = viewportWithPadding 800.0 600.0 20.0
-- | let positions = grid vp 100
-- |
-- | -- Zip with your data
-- | let positioned = Array.zipWith (\pos datum -> { x: pos.x, y: pos.y, datum })
-- |                                positions myData
-- | ```
module DataViz.Layout.Pattern
  ( -- * Grid layouts
    grid
  , gridWithAspect
  , gridExact

  -- * Offset layouts
  , honeycomb
  , brick

  -- * Spiral layouts
  , phyllotaxis
  , archimedean
  , fermat

  -- * Circular layouts
  , radial
  , concentricRings
  , sunburst

  -- * Linear layouts
  , horizontal
  , vertical
  , diagonal
  , along

  -- * Layered layouts (for neural networks, etc.)
  , layered
  , layeredCentered

  -- * Re-exports
  , module Types
  ) where

import Prelude

import Data.Array as Array
import Data.Int (floor, toNumber, ceil)
import Data.Number (sqrt, pi, cos, sin)
import DataViz.Layout.Pattern.Types (Point, Viewport, usableArea)
import DataViz.Layout.Pattern.Types (Point, Viewport, Padding, viewport, viewportWithPadding, usableArea, uniformPadding, padding, noPadding) as Types

-- =============================================================================
-- Grid Layouts
-- =============================================================================

-- | Lay out N items in a grid, automatically choosing rows/columns
-- | to best fit the viewport's aspect ratio.
-- |
-- | Items are centered within the viewport and evenly spaced.
grid :: Viewport -> Int -> Array Point
grid vp n =
  let
    area = usableArea vp
    aspect = area.width / area.height

    -- Choose columns to match aspect ratio
    -- cols/rows ≈ aspect, and cols * rows ≥ n
    cols = max 1 $ ceil $ sqrt (toNumber n * aspect)
    rows = max 1 $ ceil (toNumber n / toNumber cols)

    -- Cell dimensions
    cellW = area.width / toNumber cols
    cellH = area.height / toNumber rows

    -- Center items within cells
    offsetX = cellW / 2.0
    offsetY = cellH / 2.0
  in
    Array.mapWithIndex
      (\i _ ->
        let
          col = i `mod` cols
          row = i / cols
        in
          { x: area.x + toNumber col * cellW + offsetX
          , y: area.y + toNumber row * cellH + offsetY
          }
      )
      (Array.replicate n unit)

-- | Grid with a specific target aspect ratio for cells (width/height)
gridWithAspect :: Number -> Viewport -> Int -> Array Point
gridWithAspect cellAspect vp n =
  let
    area = usableArea vp
    viewAspect = area.width / area.height

    -- Solve for cols where cells have target aspect ratio
    -- cellW/cellH = cellAspect
    -- cellW = width/cols, cellH = height/rows
    -- rows = ceil(n/cols)
    -- So: (width/cols) / (height/ceil(n/cols)) = cellAspect
    cols = max 1 $ ceil $ sqrt (toNumber n * viewAspect / cellAspect)
    rows = max 1 $ ceil (toNumber n / toNumber cols)

    cellW = area.width / toNumber cols
    cellH = area.height / toNumber rows
    offsetX = cellW / 2.0
    offsetY = cellH / 2.0
  in
    Array.mapWithIndex
      (\i _ ->
        let
          col = i `mod` cols
          row = i / cols
        in
          { x: area.x + toNumber col * cellW + offsetX
          , y: area.y + toNumber row * cellH + offsetY
          }
      )
      (Array.replicate n unit)

-- | Grid with exact column count specified
gridExact :: Int -> Viewport -> Int -> Array Point
gridExact cols vp n =
  let
    area = usableArea vp
    rows = max 1 $ ceil (toNumber n / toNumber (max 1 cols))
    actualCols = max 1 cols

    cellW = area.width / toNumber actualCols
    cellH = area.height / toNumber rows
    offsetX = cellW / 2.0
    offsetY = cellH / 2.0
  in
    Array.mapWithIndex
      (\i _ ->
        let
          col = i `mod` actualCols
          row = i / actualCols
        in
          { x: area.x + toNumber col * cellW + offsetX
          , y: area.y + toNumber row * cellH + offsetY
          }
      )
      (Array.replicate n unit)

-- =============================================================================
-- Offset Layouts (Honeycomb, Brick)
-- =============================================================================

-- | Honeycomb layout - offset alternating rows for hexagonal packing
-- | More compact than a regular grid for circular items.
honeycomb :: Viewport -> Int -> Array Point
honeycomb vp n =
  let
    area = usableArea vp
    aspect = area.width / area.height

    -- Hex packing: rows are offset by half, vertical spacing is sqrt(3)/2 of horizontal
    verticalRatio = sqrt 3.0 / 2.0

    cols = max 1 $ ceil $ sqrt (toNumber n * aspect / verticalRatio)
    rows = max 1 $ ceil (toNumber n / toNumber cols)

    cellW = area.width / toNumber cols
    cellH = area.height / toNumber rows

    offsetX = cellW / 2.0
    offsetY = cellH / 2.0
  in
    Array.mapWithIndex
      (\i _ ->
        let
          col = i `mod` cols
          row = i / cols
          -- Offset odd rows by half a cell width
          rowOffset = if row `mod` 2 == 1 then cellW / 2.0 else 0.0
        in
          { x: area.x + toNumber col * cellW + offsetX + rowOffset
          , y: area.y + toNumber row * cellH + offsetY
          }
      )
      (Array.replicate n unit)

-- | Brick layout - like honeycomb but with rectangular cells
-- | Good for text labels or rectangular items.
brick :: Viewport -> Int -> Array Point
brick = honeycomb  -- Same algorithm, different typical use case

-- =============================================================================
-- Spiral Layouts
-- =============================================================================

-- | Golden angle constant (radians)
goldenAngle :: Number
goldenAngle = pi * (3.0 - sqrt 5.0)

-- | Phyllotaxis layout - golden angle spiral like sunflower seeds
-- | Produces beautiful, naturally-looking distributions.
-- | Items are placed at increasing distances from center using golden angle.
phyllotaxis :: Viewport -> Int -> Array Point
phyllotaxis vp n =
  let
    area = usableArea vp
    centerX = area.x + area.width / 2.0
    centerY = area.y + area.height / 2.0

    -- Scale to fit viewport (use smaller dimension to ensure fit)
    maxRadius = min (area.width / 2.0) (area.height / 2.0)

    -- Spacing factor - sqrt(i) gives even area distribution
    scale = maxRadius / sqrt (toNumber n)
  in
    Array.mapWithIndex
      (\i _ ->
        let
          -- Radius grows with sqrt of index for even area distribution
          r = scale * sqrt (toNumber i)
          -- Angle increases by golden angle each step
          theta = toNumber i * goldenAngle
        in
          { x: centerX + r * cos theta
          , y: centerY + r * sin theta
          }
      )
      (Array.replicate n unit)

-- | Archimedean spiral - constant spacing between arms
archimedean :: Number -> Viewport -> Int -> Array Point
archimedean spacing vp n =
  let
    area = usableArea vp
    centerX = area.x + area.width / 2.0
    centerY = area.y + area.height / 2.0
    maxRadius = min (area.width / 2.0) (area.height / 2.0)

    -- Total angle for n points
    totalAngle = toNumber n * spacing
    radiusPerRadian = maxRadius / totalAngle
  in
    Array.mapWithIndex
      (\i _ ->
        let
          theta = toNumber i * spacing
          r = theta * radiusPerRadian
        in
          { x: centerX + r * cos theta
          , y: centerY + r * sin theta
          }
      )
      (Array.replicate n unit)

-- | Fermat spiral - like phyllotaxis but with configurable divergence angle
fermat :: Number -> Viewport -> Int -> Array Point
fermat divergenceAngle vp n =
  let
    area = usableArea vp
    centerX = area.x + area.width / 2.0
    centerY = area.y + area.height / 2.0
    maxRadius = min (area.width / 2.0) (area.height / 2.0)
    scale = maxRadius / sqrt (toNumber n)
  in
    Array.mapWithIndex
      (\i _ ->
        let
          r = scale * sqrt (toNumber i)
          theta = toNumber i * divergenceAngle
        in
          { x: centerX + r * cos theta
          , y: centerY + r * sin theta
          }
      )
      (Array.replicate n unit)

-- =============================================================================
-- Circular Layouts
-- =============================================================================

-- | Radial layout - items evenly distributed around a circle
radial :: Viewport -> Int -> Array Point
radial vp n =
  let
    area = usableArea vp
    centerX = area.x + area.width / 2.0
    centerY = area.y + area.height / 2.0
    radius = min (area.width / 2.0) (area.height / 2.0) * 0.9  -- 90% to leave margin

    angleStep = 2.0 * pi / toNumber (max 1 n)
  in
    Array.mapWithIndex
      (\i _ ->
        let
          theta = toNumber i * angleStep - pi / 2.0  -- Start from top
        in
          { x: centerX + radius * cos theta
          , y: centerY + radius * sin theta
          }
      )
      (Array.replicate n unit)

-- | Concentric rings - distribute items across multiple rings
-- | Inner rings have fewer items proportional to their circumference.
concentricRings :: Int -> Viewport -> Int -> Array Point
concentricRings ringCount vp n =
  let
    area = usableArea vp
    centerX = area.x + area.width / 2.0
    centerY = area.y + area.height / 2.0
    maxRadius = min (area.width / 2.0) (area.height / 2.0) * 0.9

    -- Distribute items proportionally to ring circumference
    -- Ring k has radius (k+1)/ringCount * maxRadius
    -- Circumference proportional to radius, so items ∝ (k+1)
    totalWeight = toNumber $ (ringCount * (ringCount + 1)) / 2

    -- Calculate how many items per ring
    itemsPerRing = Array.mapWithIndex
      (\k _ ->
        let weight = toNumber (k + 1) / totalWeight
        in max 1 $ floor (toNumber n * weight + 0.5)
      )
      (Array.replicate ringCount unit)

    -- Generate points for each ring
    generateRing :: Int -> Int -> Int -> Array Point
    generateRing ringIdx _startIdx count =
      let
        radius = maxRadius * toNumber (ringIdx + 1) / toNumber ringCount
        angleStep = 2.0 * pi / toNumber (max 1 count)
      in
        Array.mapWithIndex
          (\i _ ->
            let theta = toNumber i * angleStep - pi / 2.0
            in { x: centerX + radius * cos theta
               , y: centerY + radius * sin theta
               }
          )
          (Array.replicate count unit)
  in
    -- Flatten all rings, take exactly n items
    Array.take n $ Array.concat $
      Array.mapWithIndex
        (\ringIdx count -> generateRing ringIdx 0 count)
        itemsPerRing

-- | Sunburst layout - like concentric rings but with angular sectors
sunburst :: Int -> Viewport -> Int -> Array Point
sunburst = concentricRings  -- Alias for discoverability

-- =============================================================================
-- Linear Layouts
-- =============================================================================

-- | Horizontal line across the viewport
horizontal :: Viewport -> Int -> Array Point
horizontal vp n =
  let
    area = usableArea vp
    centerY = area.y + area.height / 2.0
    step = if n <= 1 then 0.0 else area.width / toNumber (n - 1)
  in
    Array.mapWithIndex
      (\i _ -> { x: area.x + toNumber i * step, y: centerY })
      (Array.replicate n unit)

-- | Vertical line down the viewport
vertical :: Viewport -> Int -> Array Point
vertical vp n =
  let
    area = usableArea vp
    centerX = area.x + area.width / 2.0
    step = if n <= 1 then 0.0 else area.height / toNumber (n - 1)
  in
    Array.mapWithIndex
      (\i _ -> { x: centerX, y: area.y + toNumber i * step })
      (Array.replicate n unit)

-- | Diagonal from top-left to bottom-right
diagonal :: Viewport -> Int -> Array Point
diagonal vp n =
  let
    area = usableArea vp
    stepX = if n <= 1 then 0.0 else area.width / toNumber (n - 1)
    stepY = if n <= 1 then 0.0 else area.height / toNumber (n - 1)
  in
    Array.mapWithIndex
      (\i _ ->
        { x: area.x + toNumber i * stepX
        , y: area.y + toNumber i * stepY
        }
      )
      (Array.replicate n unit)

-- | Layout along an arbitrary line between two points
along :: Point -> Point -> Int -> Array Point
along start end n =
  let
    dx = end.x - start.x
    dy = end.y - start.y
    step = if n <= 1 then 0.0 else 1.0 / toNumber (n - 1)
  in
    Array.mapWithIndex
      (\i _ ->
        let t = toNumber i * step
        in { x: start.x + t * dx
           , y: start.y + t * dy
           }
      )
      (Array.replicate n unit)

-- =============================================================================
-- Layered Layouts
-- =============================================================================

-- | Layered layout - multiple horizontal rows with varying item counts.
-- | Perfect for neural networks, hierarchies, or any row-based visualization.
-- |
-- | Takes an array of item counts per layer. Returns flat array of all positions.
-- | Layers are evenly spaced vertically; items within each layer are evenly spaced
-- | horizontally across the full width.
-- |
-- | ```purescript
-- | -- Neural network: 4 inputs, 8 hidden, 8 hidden, 2 outputs
-- | let positions = layered vp [4, 8, 8, 2]
-- | ```
layered :: Viewport -> Array Int -> Array Point
layered vp layerCounts =
  let
    area = usableArea vp
    numLayers = Array.length layerCounts

    -- Vertical spacing between layers
    layerStep = if numLayers <= 1
                then 0.0
                else area.height / toNumber (numLayers - 1)

    -- Generate positions for one layer
    layerPositions :: Int -> Int -> Array Point
    layerPositions layerIdx count =
      let
        y = area.y + toNumber layerIdx * layerStep
        step = if count <= 1 then 0.0 else area.width / toNumber (count - 1)
      in
        Array.mapWithIndex
          (\i _ -> { x: area.x + toNumber i * step, y })
          (Array.replicate count unit)
  in
    Array.concat $ Array.mapWithIndex layerPositions layerCounts

-- | Layered layout with items centered in each row.
-- | Unlike `layered`, this centers items using cell-based positioning
-- | (items are centered within evenly-divided cells, not edge-to-edge).
-- |
-- | Better for when you want consistent margins at row edges.
layeredCentered :: Viewport -> Array Int -> Array Point
layeredCentered vp layerCounts =
  let
    area = usableArea vp
    numLayers = Array.length layerCounts

    -- Vertical spacing - use cells, center items within
    layerHeight = area.height / toNumber (max 1 numLayers)

    -- Generate positions for one layer
    layerPositions :: Int -> Int -> Array Point
    layerPositions layerIdx count =
      let
        y = area.y + (toNumber layerIdx + 0.5) * layerHeight
        cellWidth = area.width / toNumber (max 1 count)
      in
        Array.mapWithIndex
          (\i _ -> { x: area.x + (toNumber i + 0.5) * cellWidth, y })
          (Array.replicate count unit)
  in
    Array.concat $ Array.mapWithIndex layerPositions layerCounts
