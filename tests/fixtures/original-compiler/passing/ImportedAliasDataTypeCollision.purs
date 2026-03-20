module Main where

import Prelude

import ImportedAliasDataTypeCollision.Signal (Time)
import ImportedAliasDataTypeCollision.Lib (mkTime)
import Effect.Console (log)

-- Regression test: importing `type Time = Number` (alias) from Signal
-- while also importing values from Lib that use `Time` (data type).
-- canonical_origins must NOT rewrite the data type reference in Lib's
-- exports to a qualified form that then mismatches with the alias.

-- Time here is the alias (= Number)
delay :: Time -> Time
delay t = t + 1.0

main = log "Done"
