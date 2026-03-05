-- @shouldFailWith UnknownName
module Main where

import Lib as Q

-- Event should NOT be available unqualified since we used `import Lib as Q`
x :: Event
x = { name: "test" }
