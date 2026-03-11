module Main where

import Safe.Coerce (coerce)
import Prim.Coerce (class Coercible)
import Effect.Console (log)

-- Regression test: Coercible solver correctly handles coerce through
-- nested type constructors with newtype arguments. Previously, when
-- unsolved unification variables appeared in type constructor argument
-- positions (e.g. Map ?a (Array ?b)), the solver would incorrectly
-- emit TypesDoNotUnify or NoInstanceFound instead of deferring.

newtype Id a = Id a

newtype N = N String

data Pair a b = Pair a b
type role Pair representational representational

-- Coerce through nested type constructors (similar to Map Id (Array Response))
unwrapPair :: Pair (Id Int) (Array N) -> Pair Int (Array String)
unwrapPair = coerce

-- Coerce with inferred intermediate types:
-- Here the Coercible constraint is generated before the full type is known,
-- exercising the deferred constraint path.
convert :: Pair (Id Int) (Array N) -> Pair Int (Array String)
convert x =
  let result = coerce x
  in result

main = log "Done"
