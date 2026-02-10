-- | PSD3.Unified.DataDSL - Unified Data Operations
-- |
-- | This module provides a unified finally-tagless DSL for data operations
-- | that works across both visualization (PSD3) and spreadsheet contexts.
-- |
-- | ## Core Insight
-- |
-- | D3's data joins and spreadsheet formulas are fundamentally the same:
-- | - `selection.data(arr).join("rect")` ≈ `mapA template (source arr)`
-- | - `=SUM(A1:A10)` ≈ `foldA (+) 0 (source range)`
-- |
-- | By abstracting these operations into a type class, we enable:
-- | 1. Same computation definition for viz AND spreadsheet
-- | 2. Multiple interpreters (Eval, Deps, Pretty, CodeGen)
-- | 3. Type-safe composition across contexts
-- |
-- | ## Relationship to Existing PSD3 Classes
-- |
-- | DataDSL extends and unifies the existing expression classes:
-- | - `NumExpr` → `DataDSL` (num, add, sub, mul, div)
-- | - `BoolExpr` → `DataDSL` (bool, and, or, not, ifThenElse)
-- | - `CompareExpr` → `DataDSL` (lt, lte, gt, gte, eqNum)
-- |
-- | Plus NEW array/data operations:
-- | - `source`, `mapA`, `foldA`, `filterA`, `flatMapA`
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Define computation once
-- | growthRates :: forall repr. DataDSL repr => repr (Array Number) -> repr (Array Number)
-- | growthRates = mapA (\x -> x * 1.1)
-- |
-- | -- Use in visualization
-- | myViz = join (growthRates data) \rate -> elem Rect [height (rate * 10)]
-- |
-- | -- Use in spreadsheet
-- | myCell = format percentageD (avgA (growthRates data))
-- | ```
module Hylograph.Unified.DataDSL
  ( -- * Core Type Class
    class DataDSL
  , num
  , str
  , bool
  , arr
  , source
  , mapA
  , foldA
  , filterA
  , flatMapA
  , zipWithA
  , headA
  , add
  , sub
  , mul
  , div
  , negate
  , lt
  , lte
  , gt
  , gte
  , eqNum
  , strEq
  , strNeq
  , concat
  , and
  , or
  , not
  , ifThenElse
    -- * Trig Extension
  , class TrigDSL
  , sin
  , cos
  , tan
  , asin
  , acos
  , atan
  , atan2
  , pi
    -- * Convenience Functions
  , sumA
  , avgA
  , countA
  , maxA
  , minA
  , productA
  , absA
  , negateA
    -- * Data Sources
  , DataSource(..)
  , CellAddr
  , TypedCell(..)
    -- * Re-exports from existing classes for compatibility
  , module ReExports
  ) where

import Prelude hiding (add, sub, mul, div, not, map, negate)
import Prelude as P

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Maybe (Maybe)

-- Re-export existing expression classes for compatibility
import Hylograph.Expr.Expr (class NumExpr, class BoolExpr, class CompareExpr) as ReExports

-- =============================================================================
-- Data Sources
-- =============================================================================

-- | Cell address for spreadsheet sources
type CellAddr = { col :: Int, row :: Int }

-- | Type-safe cell reference with phantom type tracking the value type
newtype TypedCell a = TypedCell CellAddr

-- | Data source - where data enters the computation pipeline
-- |
-- | This is the "join point" - analogous to D3's selection.data()
data DataSource a
  = InlineSource (Array a)                    -- Literal data
  | RangeSource CellAddr CellAddr             -- Spreadsheet range
  | TableSource String                        -- Named table/collection
  | QuerySource String                        -- SQL or query string
  | DerivedSource String                      -- Named derived computation

-- =============================================================================
-- Core DataDSL Type Class
-- =============================================================================

-- | The unified data operations type class
-- |
-- | This class captures the fundamental operations on data that are
-- | shared between visualization and spreadsheet contexts.
-- |
-- | **Key insight**: These operations are exactly what D3 data joins do,
-- | and also what spreadsheet formulas do. They're the same thing!
class DataDSL (repr :: Type -> Type) where
  -- | Numeric literal
  num :: Number -> repr Number

  -- | String literal
  str :: String -> repr String

  -- | Boolean literal
  bool :: Boolean -> repr Boolean

  -- | Array literal
  arr :: forall a. Array a -> repr (Array a)

  -- | Data source - the "join point" where external data enters
  -- |
  -- | In D3: `selection.data(arr)`
  -- | In spreadsheet: cell range reference like `A1:A10`
  source :: forall a. DataSource a -> repr (Array a)

  -- | Map over array - the heart of D3 data joins
  -- |
  -- | In D3: The template function in `.join("rect").attr("height", d => d.value)`
  -- | In spreadsheet: `=MAP(A1:A10, x => x * 2)`
  mapA :: forall a b. (a -> b) -> repr (Array a) -> repr (Array b)

  -- | Fold/reduce array to single value
  -- |
  -- | In D3: `.data(arr).reduce((acc, d) => acc + d.value, 0)`
  -- | In spreadsheet: `=SUM(A1:A10)`, `=PRODUCT(B1:B5)`
  foldA :: forall a b. (b -> a -> b) -> b -> repr (Array a) -> repr b

  -- | Filter array by predicate
  -- |
  -- | In D3: `.data(arr.filter(d => d.value > 0))`
  -- | In spreadsheet: `=FILTER(A1:A10, x => x > 0)`
  filterA :: forall a. (a -> Boolean) -> repr (Array a) -> repr (Array a)

  -- | FlatMap - map then flatten (for nested data)
  -- |
  -- | This is the `decompose` in NestedJoin!
  -- | In D3: Nested selections
  -- | In spreadsheet: `=FLATTEN(MAP(A1:A10, x => x.items))`
  flatMapA :: forall a b. (a -> Array b) -> repr (Array a) -> repr (Array b)

  -- | Zip two arrays with combining function
  zipWithA :: forall a b c. (a -> b -> c) -> repr (Array a) -> repr (Array b) -> repr (Array c)

  -- | Get first element
  headA :: forall a. repr (Array a) -> repr (Maybe a)

  -- | Arithmetic operations (from NumExpr)
  add :: repr Number -> repr Number -> repr Number
  sub :: repr Number -> repr Number -> repr Number
  mul :: repr Number -> repr Number -> repr Number
  div :: repr Number -> repr Number -> repr Number
  negate :: repr Number -> repr Number

  -- | String operations (from StringExpr)
  concat :: repr String -> repr String -> repr String

  -- | Comparison operations (from CompareExpr)
  lt :: repr Number -> repr Number -> repr Boolean
  lte :: repr Number -> repr Number -> repr Boolean
  gt :: repr Number -> repr Number -> repr Boolean
  gte :: repr Number -> repr Number -> repr Boolean
  eqNum :: repr Number -> repr Number -> repr Boolean

  -- | String comparison (from StringCompareExpr)
  strEq :: repr String -> repr String -> repr Boolean
  strNeq :: repr String -> repr String -> repr Boolean

  -- | Boolean operations (from BoolExpr)
  and :: repr Boolean -> repr Boolean -> repr Boolean
  or :: repr Boolean -> repr Boolean -> repr Boolean
  not :: repr Boolean -> repr Boolean

  -- | Conditional
  ifThenElse :: forall a. repr Boolean -> repr a -> repr a -> repr a

-- =============================================================================
-- TrigDSL Extension
-- =============================================================================

-- | Trigonometric operations - extension for visualization-specific math
-- |
-- | Separated from DataDSL because spreadsheets rarely need trig,
-- | but polar/radial visualizations (chord diagrams, pie charts) do.
-- |
-- | ```purescript
-- | polarX :: forall repr. DataDSL repr => TrigDSL repr => repr Number -> repr Number -> repr Number
-- | polarX r angle = r `mul` cos angle
-- | ```
class DataDSL repr <= TrigDSL repr where
  sin :: repr Number -> repr Number
  cos :: repr Number -> repr Number
  tan :: repr Number -> repr Number
  asin :: repr Number -> repr Number
  acos :: repr Number -> repr Number
  atan :: repr Number -> repr Number
  atan2 :: repr Number -> repr Number -> repr Number  -- atan2(y, x)
  pi :: repr Number

-- =============================================================================
-- Convenience Functions (built on DataDSL)
-- =============================================================================

-- | Sum numeric array
-- |
-- | Spreadsheet equivalent: `=SUM(range)`
sumA :: forall repr. DataDSL repr => repr (Array Number) -> repr Number
sumA = foldA (+) 0.0

-- | Product of numeric array
-- |
-- | Spreadsheet equivalent: `=PRODUCT(range)`
productA :: forall repr. DataDSL repr => repr (Array Number) -> repr Number
productA = foldA (*) 1.0

-- | Count elements
-- |
-- | Spreadsheet equivalent: `=COUNT(range)`
countA :: forall repr a. DataDSL repr => repr (Array a) -> repr Number
countA xs = foldA (\acc _ -> acc + 1.0) 0.0 xs

-- | Average of numeric array
-- |
-- | Spreadsheet equivalent: `=AVERAGE(range)`
avgA :: forall repr. DataDSL repr => repr (Array Number) -> repr Number
avgA xs = sumA xs `div` countA xs

-- Sentinel values for max/min folds
negativeInfinity :: Number
negativeInfinity = P.negate 1.0e308

positiveInfinity :: Number
positiveInfinity = 1.0e308

-- | Maximum value
-- |
-- | Spreadsheet equivalent: `=MAX(range)`
maxA :: forall repr. DataDSL repr => repr (Array Number) -> repr Number
maxA = foldA P.max negativeInfinity

-- | Minimum value
-- |
-- | Spreadsheet equivalent: `=MIN(range)`
minA :: forall repr. DataDSL repr => repr (Array Number) -> repr Number
minA = foldA P.min positiveInfinity

-- | Absolute value
-- |
-- | Spreadsheet equivalent: `=ABS(x)`
absA :: forall repr. DataDSL repr => repr Number -> repr Number
absA x = ifThenElse (lt x (num 0.0)) (negate x) x

-- | Negate all values in array
-- |
-- | Spreadsheet equivalent: `=MAP(range, x => -x)`
negateA :: forall repr. DataDSL repr => repr (Array Number) -> repr (Array Number)
negateA = mapA P.negate
