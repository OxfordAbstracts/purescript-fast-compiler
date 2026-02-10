-- | Pure PureScript Polygon Generators
-- |
-- | Generates SVG polygon points strings for regular polygons and stars.
-- | No D3 dependency - pure trigonometry.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hylograph.Shape.Polygon (regularPolygonPoints, trianglePoints, starPoints)
-- |
-- | -- Triangle centered at (100, 100) with radius 50
-- | let points = trianglePoints 100.0 100.0 50.0
-- | -- Result: "100,50 143.3,125 56.7,125"
-- |
-- | -- Hexagon with 6 sides
-- | let hex = regularPolygonPoints 100.0 100.0 50.0 6
-- |
-- | -- 5-pointed star
-- | let star = starPoints 100.0 100.0 50.0 25.0 5
-- | ```
-- |
-- | Orientation: First vertex points upward (12 o'clock), vertices proceed clockwise.
-- | This matches D3's convention.
module Hylograph.Shape.Polygon
  ( -- * Regular Polygons
    regularPolygonPoints
    -- * Common Shapes
  , trianglePoints
  , squarePoints
  , diamondPoints
  , pentagonPoints
  , hexagonPoints
  , octagonPoints
    -- * Stars
  , starPoints
  , starPointsWithRotation
    -- * Utilities
  , pointsToString
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (intercalate)
import Data.Int (toNumber)
import Data.Number (cos, sin, pi)

-- | Two times pi
tau :: Number
tau = 2.0 * pi

-- | Generate points for a regular n-sided polygon
-- |
-- | Arguments:
-- | - `cx`: Center x coordinate
-- | - `cy`: Center y coordinate
-- | - `radius`: Distance from center to vertices
-- | - `sides`: Number of sides (3 = triangle, 4 = square, etc.)
-- |
-- | Returns: SVG points string "x1,y1 x2,y2 ..."
-- |
-- | First vertex is at 12 o'clock (pointing up), vertices proceed clockwise.
regularPolygonPoints :: Number -> Number -> Number -> Int -> String
regularPolygonPoints cx cy radius sides =
  let
    n = toNumber sides
    angleStep = tau / n
    -- Start at 12 o'clock: -π/2 in standard coordinates
    startAngle = -pi / 2.0

    vertices = Array.mapWithIndex (\i _ ->
      let angle = startAngle + (toNumber i * angleStep)
          x = cx + radius * cos angle
          y = cy + radius * sin angle
      in { x, y }
    ) (Array.replicate sides unit)
  in
    pointsToString vertices

-- | Convert array of points to SVG points string
pointsToString :: Array { x :: Number, y :: Number } -> String
pointsToString pts = intercalate " " (map (\p -> show p.x <> "," <> show p.y) pts)

-- | Equilateral triangle (3 sides)
-- | First vertex points upward
trianglePoints :: Number -> Number -> Number -> String
trianglePoints cx cy radius = regularPolygonPoints cx cy radius 3

-- | Square (4 sides)
-- | First vertex points upward (like a diamond rotated 45°)
-- | For axis-aligned square, use diamondPoints
squarePoints :: Number -> Number -> Number -> String
squarePoints cx cy radius = regularPolygonPoints cx cy radius 4

-- | Diamond (4 sides, axis-aligned)
-- | Vertices at top, right, bottom, left
-- | This is the "natural" orientation for a diamond shape
diamondPoints :: Number -> Number -> Number -> String
diamondPoints cx cy radius =
  let
    top = { x: cx, y: cy - radius }
    right = { x: cx + radius, y: cy }
    bottom = { x: cx, y: cy + radius }
    left = { x: cx - radius, y: cy }
  in
    pointsToString [top, right, bottom, left]

-- | Pentagon (5 sides)
pentagonPoints :: Number -> Number -> Number -> String
pentagonPoints cx cy radius = regularPolygonPoints cx cy radius 5

-- | Hexagon (6 sides)
-- | Flat-topped hexagon (first vertex at 12 o'clock)
hexagonPoints :: Number -> Number -> Number -> String
hexagonPoints cx cy radius = regularPolygonPoints cx cy radius 6

-- | Octagon (8 sides)
octagonPoints :: Number -> Number -> Number -> String
octagonPoints cx cy radius = regularPolygonPoints cx cy radius 8

-- | Generate points for a star shape
-- |
-- | Arguments:
-- | - `cx`: Center x coordinate
-- | - `cy`: Center y coordinate
-- | - `outerRadius`: Distance to outer points
-- | - `innerRadius`: Distance to inner points (the "valleys")
-- | - `points`: Number of points (5 = classic 5-pointed star)
-- |
-- | Returns: SVG points string for the star
-- |
-- | A star alternates between outer and inner radii. A 5-pointed star
-- | has 10 vertices (5 outer, 5 inner).
starPoints :: Number -> Number -> Number -> Number -> Int -> String
starPoints cx cy outerRadius innerRadius numPoints =
  starPointsWithRotation cx cy outerRadius innerRadius numPoints 0.0

-- | Star with custom rotation
-- |
-- | Arguments:
-- | - `cx`, `cy`: Center coordinates
-- | - `outerRadius`: Distance to outer points
-- | - `innerRadius`: Distance to inner points
-- | - `numPoints`: Number of points
-- | - `rotation`: Rotation in radians (0 = first point at 12 o'clock)
starPointsWithRotation :: Number -> Number -> Number -> Number -> Int -> Number -> String
starPointsWithRotation cx cy outerRadius innerRadius numPoints rotation =
  let
    n = toNumber numPoints
    -- Total vertices = 2 * points (alternating outer/inner)
    totalVertices = numPoints * 2
    angleStep = tau / (n * 2.0)
    -- Start at 12 o'clock plus rotation
    startAngle = -pi / 2.0 + rotation

    vertices = Array.mapWithIndex (\i _ ->
      let angle = startAngle + (toNumber i * angleStep)
          -- Alternate between outer and inner radius
          r = if i `mod` 2 == 0 then outerRadius else innerRadius
          x = cx + r * cos angle
          y = cy + r * sin angle
      in { x, y }
    ) (Array.replicate totalVertices unit)
  in
    pointsToString vertices
