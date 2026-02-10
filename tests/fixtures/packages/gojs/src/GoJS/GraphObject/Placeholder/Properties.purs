module GoJS.GraphObject.Placeholder.Properties where

import GoJS.GraphObject.Types (Placeholder_)
import GoJS.Unsafe (getUnsafe)

-- TODO: Should return a MarginLike
_padding :: Placeholder_ -> Number
_padding = getUnsafe ["padding"]