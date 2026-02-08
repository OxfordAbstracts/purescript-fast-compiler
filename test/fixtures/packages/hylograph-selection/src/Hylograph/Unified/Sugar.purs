-- | Hylograph.Unified.Sugar - Syntactic Sugar for DataDSL
-- |
-- | Operators and helpers to make expressions more readable.
-- |
-- | Compare:
-- |   add (mul xField (num 20.0)) (num 200.0)
-- | vs:
-- |   xField *: 20.0 +: 200.0
module Hylograph.Unified.Sugar
  ( -- Numeric operators
    (+.), addOp
  , (-.), subOp
  , (*.), mulOp
  , (/.), divOp
  , neg
    -- Numeric with literals on right
  , (+:), addLit
  , (-:), subLit
  , (*:), mulLit
  , (/:), divLit
    -- String operators
  , (<+>), concatOp
    -- Comparison operators (numeric)
  , (<.), ltOp
  , (<=.), lteOp
  , (>.), gtOp
  , (>=.), gteOp
  , (==.), eqOp
    -- String comparison operators
  , (===), strEqOp
  , (/==), strNeqOp
    -- Trig (re-exported from DataDSL)
  , module TrigExports
    -- Helpers
  , n
  , s
  , b
  , ite
  ) where

import Prelude hiding (add, sub, mul, div, negate, not)

import Hylograph.Unified.DataDSL (class DataDSL)
import Hylograph.Unified.DataDSL (sin, cos, tan, asin, acos, atan, atan2, pi) as TrigExports
import Hylograph.Unified.DataDSL as D

-- =============================================================================
-- Numeric Operators (repr Number -> repr Number -> repr Number)
-- =============================================================================

infixl 6 addOp as +.
infixl 6 subOp as -.
infixl 7 mulOp as *.
infixl 7 divOp as /.

addOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Number
addOp = D.add

subOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Number
subOp = D.sub

mulOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Number
mulOp = D.mul

divOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Number
divOp = D.div

neg :: forall repr. DataDSL repr => repr Number -> repr Number
neg = D.negate

-- =============================================================================
-- Numeric with literal on right (repr Number -> Number -> repr Number)
-- Allows: xField *: 20.0  instead of  xField *. num 20.0
-- =============================================================================

infixl 6 addLit as +:
infixl 6 subLit as -:
infixl 7 mulLit as *:
infixl 7 divLit as /:

addLit :: forall repr. DataDSL repr => repr Number -> Number -> repr Number
addLit x y = D.add x (D.num y)

subLit :: forall repr. DataDSL repr => repr Number -> Number -> repr Number
subLit x y = D.sub x (D.num y)

mulLit :: forall repr. DataDSL repr => repr Number -> Number -> repr Number
mulLit x y = D.mul x (D.num y)

divLit :: forall repr. DataDSL repr => repr Number -> Number -> repr Number
divLit x y = D.div x (D.num y)

-- =============================================================================
-- String Operators
-- =============================================================================

infixr 5 concatOp as <+>

concatOp :: forall repr. DataDSL repr => repr String -> repr String -> repr String
concatOp = D.concat

-- =============================================================================
-- Comparison Operators (repr Number -> repr Number -> repr Boolean)
-- =============================================================================

infix 4 ltOp as <.
infix 4 lteOp as <=.
infix 4 gtOp as >.
infix 4 gteOp as >=.
infix 4 eqOp as ==.

ltOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Boolean
ltOp = D.lt

lteOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Boolean
lteOp = D.lte

gtOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Boolean
gtOp = D.gt

gteOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Boolean
gteOp = D.gte

eqOp :: forall repr. DataDSL repr => repr Number -> repr Number -> repr Boolean
eqOp = D.eqNum

-- =============================================================================
-- String Comparison Operators (repr String -> repr String -> repr Boolean)
-- =============================================================================

infix 4 strEqOp as ===
infix 4 strNeqOp as /==

strEqOp :: forall repr. DataDSL repr => repr String -> repr String -> repr Boolean
strEqOp = D.strEq

strNeqOp :: forall repr. DataDSL repr => repr String -> repr String -> repr Boolean
strNeqOp = D.strNeq

-- =============================================================================
-- Short Helpers
-- =============================================================================

-- | Short alias for `num` - creates a numeric literal
-- | Usage: n 42.0
n :: forall repr. DataDSL repr => Number -> repr Number
n = D.num

-- | Short alias for `str` - creates a string literal
-- | Usage: s "hello"
s :: forall repr. DataDSL repr => String -> repr String
s = D.str

-- | Short alias for `bool` - creates a boolean literal
-- | Usage: b true
b :: forall repr. DataDSL repr => Boolean -> repr Boolean
b = D.bool

-- | Short alias for `ifThenElse` - conditional expression
-- | Usage: ite (x <. n 0.0) (s "negative") (s "non-negative")
ite :: forall repr a. DataDSL repr => repr Boolean -> repr a -> repr a -> repr a
ite = D.ifThenElse
