module Simple.ULID.Node
  ( prng
  ) where

import Simple.ULID.PRNG (PRNG)

foreign import prng :: PRNG
