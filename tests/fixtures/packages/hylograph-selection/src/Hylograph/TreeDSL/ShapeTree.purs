-- | Hylograph.TreeDSL.ShapeTree - Heterogeneous Shape Rendering Extension
-- |
-- | This module extends TreeDSL with support for rendering heterogeneous
-- | shapes - trees where nodes can be circles, rectangles, polygons, tables,
-- | or any other visual form depending on the data.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hylograph.TreeDSL.ShapeTree
-- |
-- | myViz :: forall tree. ShapeTreeDSL tree => tree NodeData
-- | myViz = joinData "nodes" "g" nodes $ \node ->
-- |   fromShapeSpec (_.shape) (nodeDimensions node)
-- | ```
-- |
-- | ## Design
-- |
-- | `ShapeSpec` is an ADT describing visual forms. Each constructor carries
-- | the attributes needed to render that form. The `fromShapeSpec` method
-- | takes a function that extracts a ShapeSpec from your datum.
-- |
-- | This is an EXTENSION - it doesn't modify the core TreeDSL class.
-- | Interpreters opt-in by implementing ShapeTreeDSL.
-- |
module Hylograph.TreeDSL.ShapeTree
  ( class ShapeTreeDSL
  , fromShapeSpec
  -- * Shape Specification
  , ShapeSpec(..)
  , Dimensions
  -- * Shape Predicates
  , isCircleSpec
  , isRectSpec
  , isPolygonSpec
  , isTableSpec
  , isGroupSpec
  -- * Convenience Constructors
  , circleSpec
  , rectSpec
  , polygonSpec
  , tableSpec
  , groupSpec
  ) where

import Prelude

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Hylograph.AST (Tree)
import Hylograph.AST as AST
import Hylograph.Internal.Attribute (Attribute(..), AttributeName(..), AttributeValue(..), AttrSource(..))
import Hylograph.Internal.Selection.Types (ElementType(..))
import Hylograph.TreeDSL (class TreeDSL, elem, withChildren, conditionalRender)

-- =============================================================================
-- Dimensions (for layout)
-- =============================================================================

-- | Dimensions for layout calculations.
-- |
-- | Layout algorithms need to know the size of each node before
-- | positioning them. This record provides that information.
type Dimensions =
  { width :: Number
  , height :: Number
  }

-- =============================================================================
-- ShapeSpec ADT
-- =============================================================================

-- | Specification for a visual shape.
-- |
-- | Each constructor represents a different visual form with its
-- | own set of attributes. The `datum` parameter allows attributes
-- | to be computed from data.
-- |
-- | This is intentionally a closed ADT - it defines a "vocabulary"
-- | of visual primitives. Extensions can add new shape types by
-- | creating additional ShapeTreeDSL-like classes.
data ShapeSpec datum
  = CircleSpec
      { radius :: datum -> Number
      , fill :: datum -> String
      , stroke :: datum -> Maybe String
      , strokeWidth :: datum -> Maybe Number
      }
  | RectSpec
      { width :: datum -> Number
      , height :: datum -> Number
      , fill :: datum -> String
      , stroke :: datum -> Maybe String
      , strokeWidth :: datum -> Maybe Number
      , cornerRadius :: datum -> Maybe Number
      }
  | PolygonSpec
      { points :: datum -> String  -- SVG points format: "x1,y1 x2,y2 x3,y3"
      , fill :: datum -> String
      , stroke :: datum -> Maybe String
      , strokeWidth :: datum -> Maybe Number
      }
  | TableSpec
      { rows :: datum -> Array (Array String)
      , headerFill :: datum -> String
      , cellFill :: datum -> String
      , textColor :: datum -> String
      , cellPadding :: datum -> Number
      }
  | GroupSpec
      { children :: Array (ShapeSpec datum)
      }

-- =============================================================================
-- Shape Predicates
-- =============================================================================

isCircleSpec :: forall d. ShapeSpec d -> Boolean
isCircleSpec (CircleSpec _) = true
isCircleSpec _ = false

isRectSpec :: forall d. ShapeSpec d -> Boolean
isRectSpec (RectSpec _) = true
isRectSpec _ = false

isPolygonSpec :: forall d. ShapeSpec d -> Boolean
isPolygonSpec (PolygonSpec _) = true
isPolygonSpec _ = false

isTableSpec :: forall d. ShapeSpec d -> Boolean
isTableSpec (TableSpec _) = true
isTableSpec _ = false

isGroupSpec :: forall d. ShapeSpec d -> Boolean
isGroupSpec (GroupSpec _) = true
isGroupSpec _ = false

-- =============================================================================
-- Convenience Constructors
-- =============================================================================

-- | Create a circle spec with sensible defaults.
circleSpec
  :: forall d
   . { radius :: d -> Number, fill :: d -> String }
  -> ShapeSpec d
circleSpec { radius, fill } = CircleSpec
  { radius
  , fill
  , stroke: const Nothing
  , strokeWidth: const Nothing
  }

-- | Create a rect spec with sensible defaults.
rectSpec
  :: forall d
   . { width :: d -> Number, height :: d -> Number, fill :: d -> String }
  -> ShapeSpec d
rectSpec { width, height, fill } = RectSpec
  { width
  , height
  , fill
  , stroke: const Nothing
  , strokeWidth: const Nothing
  , cornerRadius: const Nothing
  }

-- | Create a polygon spec with sensible defaults.
polygonSpec
  :: forall d
   . { points :: d -> String, fill :: d -> String }
  -> ShapeSpec d
polygonSpec { points, fill } = PolygonSpec
  { points
  , fill
  , stroke: const Nothing
  , strokeWidth: const Nothing
  }

-- | Create a table spec with sensible defaults.
tableSpec
  :: forall d
   . { rows :: d -> Array (Array String) }
  -> ShapeSpec d
tableSpec { rows } = TableSpec
  { rows
  , headerFill: const "#4d8bf5"
  , cellFill: const "#ffffff"
  , textColor: const "#111111"
  , cellPadding: const 4.0
  }

-- | Create a group spec (container for multiple shapes).
groupSpec :: forall d. Array (ShapeSpec d) -> ShapeSpec d
groupSpec children = GroupSpec { children }

-- =============================================================================
-- ShapeTreeDSL Typeclass
-- =============================================================================

-- | Extension for heterogeneous shape rendering.
-- |
-- | This class adds the ability to render different visual forms
-- | based on a ShapeSpec extracted from each datum.
-- |
-- | The `dimensions` function is required for layout - it tells
-- | layout algorithms how much space each node needs.
class TreeDSL tree <= ShapeTreeDSL tree where

  -- | Render a shape based on a specification extracted from datum.
  -- |
  -- | Example:
  -- | ```purescript
  -- | joinData "nodes" "g" nodes $ \node ->
  -- |   fromShapeSpec
  -- |     (_.visual)  -- extract ShapeSpec from datum
  -- |     (\d -> { width: 50.0, height: 50.0 })  -- dimensions for layout
  -- | ```
  fromShapeSpec
    :: forall datum
     . (datum -> ShapeSpec datum)   -- Extract shape spec from datum
    -> (datum -> Dimensions)        -- Dimensions for layout
    -> tree datum

-- =============================================================================
-- Tree Instance
-- =============================================================================

-- | ShapeTreeDSL instance for Tree.
-- |
-- | Implements shape rendering by converting to ConditionalRender.
-- | Each shape type becomes a predicate/spec pair.
instance ShapeTreeDSL Tree where
  fromShapeSpec getSpec _dimensions = conditionalRender
    [ -- Circle
      { predicate: \d -> isCircleSpec (getSpec d)
      , spec: \d -> case getSpec d of
          CircleSpec r -> elem Circle (circleAttrs r)
          _ -> elem Group []
      }
    -- Rectangle
    , { predicate: \d -> isRectSpec (getSpec d)
      , spec: \d -> case getSpec d of
          RectSpec r -> elem Rect (rectAttrs r)
          _ -> elem Group []
      }
    -- Polygon (rendered as Path)
    , { predicate: \d -> isPolygonSpec (getSpec d)
      , spec: \d -> case getSpec d of
          PolygonSpec r -> elem Path (pathAttrs r)
          _ -> elem Group []
      }
    -- Table (rendered as foreignObject with HTML table, or as SVG rects/text)
    , { predicate: \d -> isTableSpec (getSpec d)
      , spec: \d -> case getSpec d of
          TableSpec r -> renderTable r d
          _ -> elem Group []
      }
    -- Group (recursive)
    , { predicate: \d -> isGroupSpec (getSpec d)
      , spec: \d -> case getSpec d of
          GroupSpec r -> elem Group [] `withChildren`
            (map (\childSpec -> fromShapeSpec (const childSpec) _dimensions) r.children)
          _ -> elem Group []
      }
    ]

-- =============================================================================
-- Attribute Builders (internal)
-- =============================================================================

-- | Build circle attributes from spec
circleAttrs
  :: forall d
   . { radius :: d -> Number
     , fill :: d -> String
     , stroke :: d -> Maybe String
     , strokeWidth :: d -> Maybe Number
     }
  -> Array (Attribute d)
circleAttrs spec =
  [ dataAttr "r" (NumberValue <<< spec.radius)
  , dataAttr "fill" (StringValue <<< spec.fill)
  ]
  <> maybeDataAttr "stroke" StringValue (spec.stroke)
  <> maybeDataAttr "stroke-width" NumberValue (spec.strokeWidth)

-- | Build rect attributes from spec
rectAttrs
  :: forall d
   . { width :: d -> Number
     , height :: d -> Number
     , fill :: d -> String
     , stroke :: d -> Maybe String
     , strokeWidth :: d -> Maybe Number
     , cornerRadius :: d -> Maybe Number
     }
  -> Array (Attribute d)
rectAttrs spec =
  [ -- Center the rect on its position (SVG rect draws from top-left)
    dataAttr "x" (\d -> NumberValue $ -(spec.width d) / 2.0)
  , dataAttr "y" (\d -> NumberValue $ -(spec.height d) / 2.0)
  , dataAttr "width" (NumberValue <<< spec.width)
  , dataAttr "height" (NumberValue <<< spec.height)
  , dataAttr "fill" (StringValue <<< spec.fill)
  ]
  <> maybeDataAttr "stroke" StringValue (spec.stroke)
  <> maybeDataAttr "stroke-width" NumberValue (spec.strokeWidth)
  <> maybeDataAttr "rx" NumberValue (spec.cornerRadius)

-- | Build path attributes from polygon spec (polygons rendered as paths)
pathAttrs
  :: forall d
   . { points :: d -> String
     , fill :: d -> String
     , stroke :: d -> Maybe String
     , strokeWidth :: d -> Maybe Number
     }
  -> Array (Attribute d)
pathAttrs spec =
  -- Convert points "x1,y1 x2,y2 x3,y3" to path "M x1,y1 L x2,y2 L x3,y3 Z"
  [ dataAttr "d" (StringValue <<< pointsToPath <<< spec.points)
  , dataAttr "fill" (StringValue <<< spec.fill)
  ]
  <> maybeDataAttr "stroke" StringValue (spec.stroke)
  <> maybeDataAttr "stroke-width" NumberValue (spec.strokeWidth)
  where
  pointsToPath :: String -> String
  pointsToPath pts = "M " <> pts <> " Z"

-- | Helper: create a data-driven attribute
dataAttr :: forall d. String -> (d -> AttributeValue) -> Attribute d
dataAttr name f = DataAttr (AttributeName name) UnknownSource f

-- | Helper: create an optional data-driven attribute
maybeDataAttr
  :: forall d a
   . String
  -> (a -> AttributeValue)
  -> (d -> Maybe a)
  -> Array (Attribute d)
maybeDataAttr name toVal getMaybe =
  [ DataAttr (AttributeName name) UnknownSource $ \d ->
      case getMaybe d of
        Just a -> toVal a
        Nothing -> StringValue ""  -- Empty string = no attribute (D3 behavior)
  ]

-- | Render a table as SVG rects and text elements.
-- | Creates a grid of cells with text content.
renderTable
  :: forall d
   . { rows :: d -> Array (Array String)
     , headerFill :: d -> String
     , cellFill :: d -> String
     , textColor :: d -> String
     , cellPadding :: d -> Number
     }
  -> d
  -> AST.Tree d
renderTable spec d =
  let
    rows = spec.rows d
    cellWidth = 50.0
    cellHeight = 20.0

    -- Compute total dimensions for centering
    numRows = Array.length rows
    numCols = case Array.head rows of
      Just firstRow -> Array.length firstRow
      Nothing -> 1
    totalWidth = Int.toNumber numCols * cellWidth
    totalHeight = Int.toNumber numRows * cellHeight

    -- Build all row groups
    rowGroups = Array.mapWithIndex (renderRow cellWidth cellHeight) rows

    -- Render a single row at vertical offset
    renderRow :: Number -> Number -> Int -> Array String -> AST.Tree d
    renderRow cw ch rowIdx cells =
      let
        yOffset = Int.toNumber rowIdx * ch
        isHeader = rowIdx == 0
        fill = if isHeader then spec.headerFill d else spec.cellFill d
        cellGroups = Array.mapWithIndex (renderCell cw ch yOffset fill) cells
      in
        elem Group
          [ dataAttr "class" (const $ StringValue $ "table-row row-" <> show rowIdx) ]
          `withChildren` cellGroups

    -- Render a single cell
    renderCell :: Number -> Number -> Number -> String -> Int -> String -> AST.Tree d
    renderCell cw ch yOff fill colIdx cellText =
      let
        xOffset = Int.toNumber colIdx * cw
      in
        elem Group
          [ dataAttr "transform" (const $ StringValue $ "translate(" <> show xOffset <> "," <> show yOff <> ")") ]
          `withChildren`
            [ -- Cell background
              elem Rect
                [ dataAttr "width" (const $ NumberValue cw)
                , dataAttr "height" (const $ NumberValue ch)
                , dataAttr "fill" (const $ StringValue fill)
                , dataAttr "stroke" (const $ StringValue "#111")
                , dataAttr "stroke-width" (const $ NumberValue 0.5)
                ]
            -- Cell text
            , elem Text
                [ dataAttr "x" (const $ NumberValue (cw / 2.0))
                , dataAttr "y" (const $ NumberValue (ch / 2.0 + 4.0))  -- +4 for baseline
                , dataAttr "text-anchor" (const $ StringValue "middle")
                , dataAttr "font-size" (const $ StringValue "10px")
                , dataAttr "font-family" (const $ StringValue "Helvetica, sans-serif")
                , dataAttr "fill" (const $ StringValue (spec.textColor d))
                , dataAttr "textContent" (const $ StringValue cellText)
                ]
            ]
  in
    -- Outer group with centering transform
    elem Group
      [ dataAttr "class" (const $ StringValue "table-shape")
      , dataAttr "transform" (const $ StringValue $
          "translate(" <> show (-(totalWidth / 2.0)) <> "," <> show (-(totalHeight / 2.0)) <> ")")
      ]
      `withChildren` rowGroups
