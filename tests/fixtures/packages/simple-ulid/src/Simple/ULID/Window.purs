module Simple.ULID.Window
  ( prng
  ) where

import Simple.ULID.PRNG (PRNG)

foreign import prng :: PRNG
