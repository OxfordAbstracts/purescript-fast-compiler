module Main where

import ConZeroBlockerExport.DataModule (T(..))
import ConZeroBlockerExport.Middle (event)

-- Regression test: when Middle module imports both `type T = { ... }`
-- (alias) and `data T` (data type), its exported value scheme for
-- `event` must preserve the data type reference, not expand it to the record.
-- This module then uses the data type T without conflict.

test :: T
test = event { name: "test", pt: PT "hello" 42 }
