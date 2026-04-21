module Shared where

-- A type alias imported by the main module that references `Model` in its body.
-- This simulates alias bodies from imported modules containing Con("Model").
type ModelExt r = { name :: String, count :: Int | r }
