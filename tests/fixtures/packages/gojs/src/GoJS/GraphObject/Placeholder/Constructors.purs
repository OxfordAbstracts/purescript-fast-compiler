module GoJS.GraphObject.Placeholder.Constructors where

import Effect (Effect)
import GoJS.GraphObject.Types (Placeholder_)
import GoJS.Unsafe (constructor0)

newPlaceholder :: Effect Placeholder_
newPlaceholder = constructor0 "Placeholder"