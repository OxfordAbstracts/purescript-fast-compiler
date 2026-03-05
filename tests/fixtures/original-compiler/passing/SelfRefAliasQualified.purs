module Main where

import Lib as Lib

-- Local alias named "Model" that references Lib.Model.
-- The qualified reference Lib.Model should NOT be treated as
-- self-referential just because the unqualified name matches.
type Model = Lib.Model

test :: Model
test = { x: 42 }
