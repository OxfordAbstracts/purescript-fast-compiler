module Main where

-- Reproducer for the Accum-alias expansion bug. `Accum s a`
-- expands to `{ accum :: s, value :: a }`; code that constructs
-- a record literal and passes it to a function whose signature
-- says `Accum s a` must unify Record↔Record, not Record↔Accum.

type Accum s a = { accum :: s, value :: a }

mk :: Int -> Accum Int Int
mk x = { accum: x, value: x }

useIt :: forall s. (Int -> Accum s Int) -> Int -> s
useIt f x = (f x).accum
