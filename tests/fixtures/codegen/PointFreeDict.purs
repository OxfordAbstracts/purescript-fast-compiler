-- Tests dict resolution for point-free (value-level) bindings vs function bindings.
-- Bug pattern: parameterized instance dict arguments dropped for point-free values.
-- When a value (not a function) uses a class method, the codegen must still fully
-- resolve all dict arguments including constraint args on parameterized instances.
module PointFreeDict where

import Prelude

-- A point-free value that uses a class method with a concrete type.
-- The dict should be fully resolved at the call site.
pointFreeShow :: String
pointFreeShow = show 42

-- Same thing but as a function (this typically works correctly)
functionShow :: Int -> String
functionShow x = show x

-- Point-free composition using class methods
pointFreeAppend :: String
pointFreeAppend = append "hello" " world"

test = pointFreeAppend

-- TEST: "hello world"
