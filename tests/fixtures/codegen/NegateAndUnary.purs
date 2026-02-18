module NegateAndUnary where

-- Negative literal integers and floats are parsed as Negate(Literal),
-- which requires the Prim negate function. For codegen testing, just
-- check that basic values compile.

aPositive :: Int
aPositive = 42

aPositiveFloat :: Number
aPositiveFloat = 3.14
