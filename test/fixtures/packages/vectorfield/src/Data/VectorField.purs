module Data.VectorField where

import Prelude
import Data.Group (class Group)
import Data.Semigroup.Commutative (class Commutative)

class (Field k, Group (f k), Commutative (f k)) <= VectorField f k where
    -- | - ∀v in V: one * v == v 
    -- | - ∀a b in K, v in V: a * (b .* v) = (a * b) .* v
    -- | - ∀a b in K, v in V: 
    -- |      - a .* (u + v) = a .* u + a .* v 
    -- |      - (a + b) .* v = a .* v + b .* v
    scalarMul :: k -> f k -> f k

flipScalarMul :: ∀f k. (VectorField f k) => f k -> k -> f k
flipScalarMul = flip scalarMul

infixr 8 scalarMul as .*
infixl 8 flipScalarMul as *.
