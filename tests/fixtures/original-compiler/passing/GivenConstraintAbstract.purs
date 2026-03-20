module Main where

import Effect.Console (log)

class Foo a

-- The Foo constraint is fully abstract (all type vars).
-- It should be treated as "given" by the signature and
-- not produce NoInstanceFound even though Foo has no instances.
bar :: forall a. Foo a => a -> Int
bar _ = 0

main = log "Done"
