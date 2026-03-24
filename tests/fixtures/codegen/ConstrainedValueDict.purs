-- Tests constrained value-level declarations (not functions).
-- Bug pattern: when a top-level value has constraints, the dict arguments
-- must be properly threaded. This is the pattern behind
-- `exitContext = P $ lift $ modify_ $ Array.drop 1` where modify_ needs
-- a MonadState dict that has a Monad constraint argument.
module ConstrainedValueDict where

import Prelude

class MyState s m where
  myGet :: m s
  myPut :: s -> m Unit

-- A constrained value (not a function) that uses a class method.
-- The codegen must generate a function that takes the dict argument.
getValue :: forall s m. MyState s m => m s
getValue = myGet

-- Use show through a constrained value
showIt :: forall a. Show a => a -> String
showIt = show

test = showIt 42

-- TEST: "42"
