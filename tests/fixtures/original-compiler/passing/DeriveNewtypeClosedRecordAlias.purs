module Main where

-- Regression test: a closed record type alias using row composition
-- should not be rejected as an open record in instance heads.
-- Previously, { | Row () } expanded to Record([], Some(Record(fields, Some(Record([], None)))))
-- which was incorrectly flagged as an open record due to the Some(_) tail.

class MonadAsk r m where
  ask :: m r

data FixM a = FixM a

type EnvRow r = (name :: String, count :: Int | r)
type Env = { | EnvRow () }

instance MonadAsk Env FixM where
  ask = FixM { name: "", count: 0 }
