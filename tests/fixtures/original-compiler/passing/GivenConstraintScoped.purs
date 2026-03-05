module Main where

import GivenConstraintScoped.Lib (class Cl, member)

-- Regression test: per-function given class scoping.
-- `handler` has `Cl m =>` in its signature, so Super (superclass of Cl)
-- is transitively "given" — calling member (needs Super) should work.

handler :: forall m. Cl m => String -> m String
handler key = member key
