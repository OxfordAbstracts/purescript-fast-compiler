module XTerm.Utils where

import Data.Function (($))
import Data.Maybe (Maybe(..))
import Foreign (Foreign, isUndefined, unsafeFromForeign)


maybeUndefined :: forall a . Foreign -> Maybe a
maybeUndefined f | isUndefined f = Nothing
maybeUndefined f = Just $ unsafeFromForeign f

