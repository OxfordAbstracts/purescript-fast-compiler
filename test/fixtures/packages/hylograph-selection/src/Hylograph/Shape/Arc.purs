-- | Pure PureScript Arc Generator
-- |
-- | Creates SVG path data for circular/annular sectors (pie slices, donut segments).
-- | No D3 dependency - pure trigonometry.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hylograph.Shape.Arc (arcPath, ArcDatum)
-- |
-- | -- Pie slice (inner radius = 0)
-- | let path = arcPath { innerRadius: 0.0, outerRadius: 100.0 }
-- |       { startAngle: 0.0, endAngle: Math.pi / 2.0 }
-- |
-- | -- Donut segment (inner radius > 0)
-- | let path = arcPath { innerRadius: 50.0, outerRadius: 100.0 }
-- |       { startAngle: 0.0, endAngle: Math.pi / 2.0 }
-- | ```
-- |
-- | Angles are in radians, with 0 at 12 o'clock, increasing clockwise.
-- | This matches D3's convention.
module Hylograph.Shape.Arc
  ( -- * Types
    ArcConfig
  , ArcDatum
    -- * Arc Path Generation
  , arcPath
  , arcPathWithCenter
    -- * Utilities
  , degreesToRadians
  , tau
  ) where

import Prelude

import Data.Number (cos, sin, pi)

-- | Configuration for arc generation (static per chart)
type ArcConfig =
  { innerRadius :: Number  -- ^ Inner radius (0 for pie, > 0 for donut)
  , outerRadius :: Number  -- ^ Outer radius
  }

-- | Per-slice data (typically from pie layout)
type ArcDatum =
  { startAngle :: Number  -- ^ Start angle in radians (0 = 12 o'clock)
  , endAngle :: Number    -- ^ End angle in radians
  }

-- | Full circle in radians
tau :: Number
tau = 2.0 * pi

-- | Convert degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Generate SVG path data for an arc sector
-- |
-- | The path creates a "pie slice" or "donut segment" shape:
-- | - Outer arc from startAngle to endAngle
-- | - Line (or inner arc) back to start
-- |
-- | Angles follow D3 convention: 0 = 12 o'clock, increasing clockwise.
arcPath :: ArcConfig -> ArcDatum -> String
arcPath = arcPathWithCenter 0.0 0.0

-- | Generate arc path centered at a specific point
arcPathWithCenter :: Number -> Number -> ArcConfig -> ArcDatum -> String
arcPathWithCenter cx cy config datum =
  let
    { innerRadius, outerRadius } = config
    { startAngle, endAngle } = datum

    -- D3 convention: 0 = 12 o'clock, clockwise
    -- SVG convention: 0 = 3 o'clock, counterclockwise
    -- Transform: rotate -90° and negate
    toSvgAngle angle = angle - pi / 2.0

    sa = toSvgAngle startAngle
    ea = toSvgAngle endAngle

    -- Calculate points
    -- Outer arc: start and end points
    outerStartX = cx + outerRadius * cos sa
    outerStartY = cy + outerRadius * sin sa
    outerEndX = cx + outerRadius * cos ea
    outerEndY = cy + outerRadius * sin ea

    -- Inner arc: start and end points (for donut)
    innerStartX = cx + innerRadius * cos sa
    innerStartY = cy + innerRadius * sin sa
    innerEndX = cx + innerRadius * cos ea
    innerEndY = cy + innerRadius * sin ea

    -- Arc flags
    angleDiff = endAngle - startAngle
    largeArcFlag = if angleDiff > pi then "1" else "0"
    sweepFlag = "1"  -- Clockwise

    -- Handle full circle (or nearly full)
    isFullCircle = angleDiff >= tau - 0.0001

  in
    if isFullCircle then
      -- Full circle needs two arcs (SVG limitation)
      fullCirclePath cx cy innerRadius outerRadius
    else if innerRadius < 0.0001 then
      -- Pie slice (no inner radius)
      pieSlicePath outerStartX outerStartY outerEndX outerEndY
                   outerRadius largeArcFlag sweepFlag cx cy
    else
      -- Donut segment
      donutSegmentPath outerStartX outerStartY outerEndX outerEndY
                       innerStartX innerStartY innerEndX innerEndY
                       outerRadius innerRadius largeArcFlag sweepFlag

-- | Path for a pie slice (innerRadius = 0)
pieSlicePath :: Number -> Number -> Number -> Number
             -> Number -> String -> String -> Number -> Number -> String
pieSlicePath x0 y0 x1 y1 r largeArc sweep cx cy =
  "M" <> show x0 <> "," <> show y0 <>
  "A" <> show r <> "," <> show r <> " 0 " <> largeArc <> "," <> sweep <> " " <> show x1 <> "," <> show y1 <>
  "L" <> show cx <> "," <> show cy <>
  "Z"

-- | Path for a donut segment (innerRadius > 0)
donutSegmentPath :: Number -> Number -> Number -> Number
                 -> Number -> Number -> Number -> Number
                 -> Number -> Number -> String -> String -> String
donutSegmentPath ox0 oy0 ox1 oy1 ix0 iy0 ix1 iy1 outerR innerR largeArc sweep =
  -- Outer arc (clockwise)
  "M" <> show ox0 <> "," <> show oy0 <>
  "A" <> show outerR <> "," <> show outerR <> " 0 " <> largeArc <> "," <> sweep <> " " <> show ox1 <> "," <> show oy1 <>
  -- Line to inner arc end
  "L" <> show ix1 <> "," <> show iy1 <>
  -- Inner arc (counterclockwise = sweep 0)
  "A" <> show innerR <> "," <> show innerR <> " 0 " <> largeArc <> ",0 " <> show ix0 <> "," <> show iy0 <>
  "Z"

-- | Full circle path (needs two semicircles due to SVG arc limitations)
fullCirclePath :: Number -> Number -> Number -> Number -> String
fullCirclePath cx cy innerR outerR =
  let
    -- Two semicircle arcs for outer
    outerTop = show cx <> "," <> show (cy - outerR)
    outerBottom = show cx <> "," <> show (cy + outerR)
    -- Two semicircle arcs for inner
    innerTop = show cx <> "," <> show (cy - innerR)
    innerBottom = show cx <> "," <> show (cy + innerR)
  in
    if innerR < 0.0001 then
      -- Full pie (circle)
      "M" <> outerTop <>
      "A" <> show outerR <> "," <> show outerR <> " 0 1,1 " <> outerBottom <>
      "A" <> show outerR <> "," <> show outerR <> " 0 1,1 " <> outerTop <>
      "Z"
    else
      -- Full donut (annulus)
      "M" <> outerTop <>
      "A" <> show outerR <> "," <> show outerR <> " 0 1,1 " <> outerBottom <>
      "A" <> show outerR <> "," <> show outerR <> " 0 1,1 " <> outerTop <>
      "M" <> innerTop <>
      "A" <> show innerR <> "," <> show innerR <> " 0 1,0 " <> innerBottom <>
      "A" <> show innerR <> "," <> show innerR <> " 0 1,0 " <> innerTop <>
      "Z"
