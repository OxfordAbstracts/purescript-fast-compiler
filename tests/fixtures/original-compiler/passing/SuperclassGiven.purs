module Main where

import SuperclassGiven.Lib (class Cl, member)
import Effect.Console (log)

-- Regression test: when a function's type signature has `Cl m =>`,
-- and Cl has superclass `Super m`, calling Super methods should not
-- produce NoInstanceFound errors. The Super constraint is transitively
-- "given" through the Cl superclass chain.

handler :: forall m. Cl m => String -> m Int
handler key = member { key }

main = log "Done"
