module GoJS.Model.ChangedEvent.Constructors where

import Effect (Effect)
import GoJS.Model.Types (ChangedEvent_)
import GoJS.Unsafe (constructor0)

newChangedEvent :: Effect ChangedEvent_
newChangedEvent = constructor0 "ChangedEvent"