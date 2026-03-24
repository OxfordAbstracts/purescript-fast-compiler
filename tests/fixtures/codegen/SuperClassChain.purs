-- Tests superclass accessor chain resolution.
-- Bug pattern: dictMonoid.Semigroup0 is not a function.
-- When a function uses a method from a superclass (e.g., append from Semigroup
-- accessed via a Monoid constraint), the codegen must generate the accessor chain.
module SuperClassChain where

import Prelude

-- Use append (from Semigroup) via a Monoid constraint.
-- This requires the codegen to generate: dictMonoid.Semigroup0() to get the Semigroup dict.
joinWithMonoid :: forall m. Monoid m => m -> m -> m
joinWithMonoid a b = append a (append mempty b)

test = joinWithMonoid "hello" " world"

-- TEST: "hello world"
