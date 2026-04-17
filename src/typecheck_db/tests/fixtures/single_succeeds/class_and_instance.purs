module Test.ClassAndInstance where

-- Two-constructor ADT so we can use it to drive an instance.
data Mood = Happy | Sad

-- Simple class with one method.
class Show a where
  show :: a -> String

-- Instance whose constraint shows up at every call site via
-- `instantiate_and_record_constraints`, then gets discharged by
-- the Phase B solver.
instance Show Mood where
  show Happy = "happy"
  show Sad = "sad"

-- Using the class method: `show Happy` triggers `Show Mood`,
-- which the solver matches against the instance above.
showIt :: String
showIt = show Happy
