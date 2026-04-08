module Ops where

-- Defines operator / with infixr 1 (right-associative, low precedence).
-- Data.EuclideanRing also defines / as infixl 7.
-- The module that imports Ops should use Ops's fixity for /.

class MySep a b c | a b -> c where
  mysep :: a -> b -> c

instance mysepIntInt :: MySep Int Int (Array Int) where
  mysep a b = [a, b]

infixr 1 mysep as /
