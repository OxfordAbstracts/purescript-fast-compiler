-- | PSD3.Unified.Examples - Examples of the Unified DSL
-- |
-- | This module demonstrates how to use the unified DSL and shows
-- | that old and new styles work together seamlessly.
-- |
-- | ## Highlights
-- |
-- | 1. **DataDSL**: Unified computations for spreadsheet and viz
-- | 2. **Display**: Profunctor-based non-destructive formatting
-- | 3. **AST Joins**: Data binding patterns for visualization
module Hylograph.Unified.Examples where

import Prelude hiding (add, sub, mul, div, not, (>>>))

import Hylograph.AST (Tree, elem, joinData, nestedJoin, updateJoin, updateNestedJoin)
import Hylograph.Internal.Selection.Types (ElementType(..))
import Hylograph.Internal.Attribute (Attribute)
import Hylograph.Unified.DataDSL (class DataDSL, mapA, foldA, filterA, sumA, avgA, source, DataSource(..))
import Data.Maybe (Maybe(..))
import Hylograph.Unified.Display (Display, runDisplay, (>>>))
import Hylograph.Unified.Display as D
import Hylograph.Unified.Attribute (attr, attrStatic)
import Hylograph.Expr.Interpreter.Eval (EvalD(..), runEvalD)

-- =============================================================================
-- Example Data Types
-- =============================================================================

type DataPoint =
  { x :: Number
  , y :: Number
  , value :: Number
  , category :: String
  }

type QuarterData =
  { quarter :: String
  , revenue :: Number
  , expenses :: Number
  }

-- =============================================================================
-- Example 1: New Style Visualization (using Display)
-- =============================================================================

-- | New-style visualization using Display profunctor
newStyleCircle :: DataPoint -> Array (Attribute DataPoint)
newStyleCircle _ =
  [ attr "cx" _.x D.showNumD
  , attr "cy" _.y D.showNumD
  , attr "r" _.value (D.roundD 1 >>> D.showNumD)
  , attr "fill" _.category D.idD
  ]

-- | With more sophisticated formatting
newStyleCircleFormatted :: DataPoint -> Array (Attribute DataPoint)
newStyleCircleFormatted _ =
  [ attr "cx" _.x (D.scaleD 10.0 >>> D.showNumD)
  , attr "cy" _.y (D.scaleD 10.0 >>> D.showNumD)
  , attr "r" _.value (D.clampD 5.0 50.0 >>> D.showNumD)
  , attr "fill" _.category D.idD
  ]

-- =============================================================================
-- Example 2: Unified Computations
-- =============================================================================

-- | A computation that works in BOTH spreadsheet and visualization contexts
computeGrowth :: forall repr. DataDSL repr =>
  repr (Array Number) -> repr (Array Number)
computeGrowth = mapA (\x -> x * 1.1)

-- | Another unified computation: filter and average
averageAboveThreshold :: forall repr. DataDSL repr =>
  Number -> repr (Array Number) -> repr Number
averageAboveThreshold threshold data_ =
  avgA (filterA (\x -> x > threshold) data_)

-- | Quarterly profit computation
computeProfit :: forall repr. DataDSL repr =>
  repr (Array QuarterData) -> repr (Array Number)
computeProfit = mapA (\q -> q.revenue - q.expenses)

-- | Total profit (works in sheet or viz)
totalProfit :: forall repr. DataDSL repr =>
  repr (Array QuarterData) -> repr Number
totalProfit quarters = sumA (computeProfit quarters)

-- =============================================================================
-- Example 3: Display Pipelines
-- =============================================================================

-- | Percentage display: 0.156 -> "15.6%"
percentDisplay :: Display Number String
percentDisplay = D.scaleD 100.0 >>> D.roundD 1 >>> D.showNumD >>> D.suffixD "%"

-- | Currency display: 1234.56 -> "$1,234.56"
currencyDisplay :: Display Number String
currencyDisplay = D.currencyD

-- | Profit display (with sign): -100 -> "(100)", 100 -> "100"
profitDisplay :: Display Number String
profitDisplay = D.signedD

-- | Compact display for large numbers: 1500000 -> "1.5M"
compactDisplay :: Display Number String
compactDisplay = D.compactD

-- | Using displays
showAsPercent :: Number -> String
showAsPercent = runDisplay percentDisplay

showAsCurrency :: Number -> String
showAsCurrency = runDisplay currencyDisplay

-- =============================================================================
-- Example 4: Display Adaptation (Profunctor power!)
-- =============================================================================

-- | Adapt percentage display to work with QuarterData
quarterGrowthDisplay :: Display QuarterData String
quarterGrowthDisplay = D.lmapD computeGrowthRate percentDisplay
  where
  computeGrowthRate q = (q.revenue - q.expenses) / q.expenses

-- | Adapt to extract different fields
revenueDisplay :: Display QuarterData String
revenueDisplay = D.lmapD _.revenue currencyDisplay

expensesDisplay :: Display QuarterData String
expensesDisplay = D.lmapD _.expenses currencyDisplay

-- =============================================================================
-- Example 5: Complete Visualization with New Style
-- =============================================================================

-- | A visualization using the new style throughout
newStyleViz :: Array DataPoint -> Tree DataPoint
newStyleViz dataPoints =
  joinData "points" "circle" dataPoints \_ ->
    elem Circle
      [ attr "cx" _.x D.showNumD
      , attr "cy" _.y D.showNumD
      , attr "r" _.value D.showNumD
      , attrStatic "fill" "steelblue"
      , attrStatic "stroke" "white"
      , attrStatic "stroke-width" "1"
      ]

-- =============================================================================
-- Example 6: The Bridge - Computation to Visualization
-- =============================================================================

-- | Define computation abstractly
myComputation :: forall repr. DataDSL repr => repr (Array Number) -> repr Number
myComputation data_ =
  avgA (filterA (\x -> x > 0.0) (mapA (\x -> x * 1.1) data_))

-- | Use in visualization context (via EvalD)
useInViz :: Array Number -> Number
useInViz data_ =
  let (EvalD f) = myComputation (source (InlineSource data_)) :: EvalD Unit Number
  in f unit 0

-- =============================================================================
-- Example 7: Formatted Labels in Visualization
-- =============================================================================

-- | Example of creating a label with display formatting
formatLabel :: QuarterData -> String
formatLabel q =
  runDisplay profitDisplay (q.revenue - q.expenses)

-- | Or with percentage growth:
formatGrowthLabel :: QuarterData -> String
formatGrowthLabel =
  runDisplay quarterGrowthDisplay

-- =============================================================================
-- Example 8: AST Join Functions
-- =============================================================================

-- | Simple data join
-- |
-- | Use `joinData` for one-shot renders where elements don't update.
-- | For dynamic updates, use `updateJoin` with a keyFn.
simpleJoinExample :: Array DataPoint -> Tree DataPoint
simpleJoinExample points =
  joinData "circles" "circle" points circleTemplate
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value D.showNumD
    , attrStatic "fill" "steelblue"
    ]

-- | Join with GUP (General Update Pattern) - enter/update/exit
-- |
-- | For dynamic updates, use `updateJoin` with a keyFn to identify elements.
-- | The keyFn extracts a unique string identifier from each datum.
joinWithGUPExample :: Array DataPoint -> Tree DataPoint
joinWithGUPExample points =
  updateJoin "circles" "circle" points circleTemplate
    { enter: Just
        { attrs:
            [ attr "r" (const 0.0) D.showNumD
            , attr "opacity" (const 0.0) D.showNumD
            ]
        , transition: Nothing  -- No transition (instant)
        }
    , update: Just { attrs: [], transition: Nothing }
    , exit: Just
        { attrs: [ attr "opacity" (const 0.0) D.showNumD ]
        , transition: Nothing
        }
    , keyFn: Just \p -> show p.x <> "," <> show p.y <> "," <> p.category
    }
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value D.showNumD
    ]

-- | Scene data with nested structure
type SceneData =
  { title :: String
  , points :: Array DataPoint
  }

-- | Nested join with type decomposition
-- |
-- | The scene data contains an array of points.
-- | `nestedJoin` extracts the inner array for joining.
-- |
-- | Use this for one-shot renders with type decomposition.
-- | For dynamic updates with decomposition, use `updateNestedJoin`.
nestedJoinExample :: SceneData -> Tree SceneData
nestedJoinExample scene =
  nestedJoin "points" "circle" [scene] _.points circleTemplate
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value D.showNumD
    ]

-- | Full join: decomposition + GUP
-- |
-- | This is the most powerful combination - handles:
-- | - Type-changing decomposition (SceneData -> Array DataPoint)
-- | - Enter/update/exit behaviors with transitions
fullJoinExample :: SceneData -> Tree SceneData
fullJoinExample scene =
  updateNestedJoin "viz" "circle" [scene] _.points circleTemplate
    { enter: Just
        { attrs: [ attr "r" (const 0.0) D.showNumD ]
        , transition: Nothing
        }
    , update: Nothing
    , exit: Just
        { attrs: [ attr "opacity" (const 0.0) D.showNumD ]
        , transition: Nothing
        }
    }
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value D.showNumD
    ]

-- =============================================================================
-- Summary
-- =============================================================================

{-
  This module demonstrates:

  1. NEW STYLE ADDS POWER
     - Composable Display pipelines
     - Type-safe adaptation with lmapD
     - Same formatting in spreadsheet and visualization

  2. UNIFIED COMPUTATIONS
     - Define with DataDSL, use anywhere
     - Same code for analysis, visualization, export
     - Type-safe across all contexts

  3. DISPLAY PROFUNCTOR
     - Compose formatting: scale >>> round >>> show >>> suffix
     - Adapt to different types: lmapD _.field display
     - Reusable across entire codebase

  4. AST JOIN FUNCTIONS
     - joinData: Basic data join for one-shot renders
     - nestedJoin: Type decomposition (outer → inner data)
     - updateJoin: GUP with keyFn for dynamic updates
     - updateNestedJoin: Decomposition + GUP combined
-}
