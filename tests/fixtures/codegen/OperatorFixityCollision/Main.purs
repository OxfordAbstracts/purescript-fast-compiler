module Main where

-- Regression: operator / from Ops (infixr 1) collided with / from
-- Data.EuclideanRing (infixl 7) in the global op_fixities map.
-- The first-registered fixity won, causing wrong associativity.
--
-- With infixr 1: (1 / 2) should associate right, so the class method
-- is called as mysep(mysepIntInt)(1)(2)
-- With infixl 7 (wrong): would parse the same but when chained with
-- other operators of different precedence, grouping would be wrong.

import Ops (mysep, (/))

-- Simple test: 1 / 2 should resolve to [1, 2]
test :: Array Int
test = 1 / 2

-- TEST: [1,2]
