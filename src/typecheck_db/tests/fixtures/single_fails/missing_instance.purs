module Test.MissingInstance where

data Mood = Happy | Sad

-- Class exists; `Show Mood` instance does NOT. The solver must
-- report NoInstanceFound rather than silently succeed.
class Show a where
  show :: a -> String

-- Reference `show` at a concrete type with no matching instance
-- in scope.
broken :: String
broken = show Happy
