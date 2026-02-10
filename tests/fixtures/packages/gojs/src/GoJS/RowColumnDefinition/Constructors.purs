module GoJS.RowColumnDefinition.Constructors where

import Effect (Effect)
import GoJS.RowColumnDefinition.Types (RowColumnDefinition_)
import GoJS.Unsafe (constructor1)

newRowColumnDefinition :: forall r. Record r -> Effect RowColumnDefinition_
newRowColumnDefinition = constructor1 "RowColumnDefinition"