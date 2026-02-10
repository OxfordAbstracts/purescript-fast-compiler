-- | PSD3.Unified - Unified Data DSL for Visualization and Computation
-- |
-- | This module re-exports the unified DSL components, providing a single
-- | import for the new unified system.
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hylograph.Unified
-- |
-- | -- Define a computation that works in both viz and spreadsheet
-- | growthAnalysis :: forall repr. DataDSL repr => repr (Array Number) -> repr Number
-- | growthAnalysis data_ = avgA (mapA (\x -> x * 1.1) data_)
-- |
-- | -- Use Display for formatting
-- | myDisplay :: Display Number String
-- | myDisplay = roundD 2 >>> showNumD >>> suffixD "%"
-- |
-- | -- Create attributes with Display
-- | myAttr :: Attribute DataPoint
-- | myAttr = attr "cx" _.x (scaleD 10.0 >>> showNumD)
-- | ```
-- |
-- | ## Module Organization
-- |
-- | - `PSD3.Unified.DataDSL` - Core type class for data operations
-- | - `PSD3.Unified.Display` - Profunctor-based display formatting
-- | - `PSD3.Unified.Attribute` - Bridge to PSD3's attribute system
-- | - `PSD3.Unified.Join` - Composable join combinators
-- | - `PSD3.Unified.Sugar` - Syntactic sugar operators
-- | - `PSD3.Unified.Interpreters.Eval` - DataDSL instances for Eval/EvalD
module Hylograph.Unified
  ( -- * DataDSL
    module DataDSL
    -- * TrigDSL
  , module TrigDSL
    -- * Display
  , module Display
    -- * Attributes
  , module Attribute
    -- * Joins
  , module Join
    -- * Sugar
  , module Sugar
  ) where

import Hylograph.Unified.DataDSL
  ( class DataDSL
  , num, str, bool, arr
  , source
  , mapA, foldA, filterA, flatMapA, zipWithA, headA
  , add, sub, mul, div, negate
  , lt, lte, gt, gte, eqNum
  , strEq, strNeq, concat
  , and, or, not
  , ifThenElse
  , sumA, avgA, countA, maxA, minA, productA, absA, negateA
  , DataSource(..)
  , CellAddr
  , TypedCell(..)
  ) as DataDSL

import Hylograph.Unified.DataDSL
  ( class TrigDSL
  , sin, cos, tan, asin, acos, atan, atan2, pi
  ) as TrigDSL

import Hylograph.Unified.Display
  ( Display(..)
  , runDisplay
  , idD, composeD, (>>>)
  , lmapD, rmapD, dimapD
  , roundD, scaleD, clampD, absD, negateD, floorD, ceilD
  , showNumD, fixedD, sciD, intD
  , prefixD, suffixD, padLeftD, padRightD, upperD, lowerD, trimD
  , percentageD, currencyD, currencyWithSymbol, thousandsD, signedD, compactD
  , boolD, yesNoD
  ) as Display

import Hylograph.Unified.Attribute
  ( attr, attrStatic, attrIndexed
  , cxD, cyD, xD, yD, rD, widthD, heightD
  , fillD, strokeD, opacityD, textContentD, transformD
  , toAttribute, fromDisplay
  ) as Attribute

import Hylograph.Unified.Join
  ( JoinSpec(..)
  , JoinConfig
  , join
  , withDecompose, Decomposer
  , withGUP, GUPSpec, PhaseSpec
  , enterSpec, updateSpec, exitSpec, noTransition
  , JoinBuilder, buildJoin
  , basicJoin, nestedJoin, gupJoin, fullJoin
  , toTree
  ) as Join

import Hylograph.Unified.Sugar
  ( (+.), addOp
  , (-.), subOp
  , (*.), mulOp
  , (/.), divOp
  , neg
  , (+:), addLit
  , (-:), subLit
  , (*:), mulLit
  , (/:), divLit
  , (<+>), concatOp
  , (<.), ltOp
  , (<=.), lteOp
  , (>.), gtOp
  , (>=.), gteOp
  , (==.), eqOp
  , (===), strEqOp
  , (/==), strNeqOp
  , n, s, b, ite
  ) as Sugar
