module GoJS.Diagram.InputEvent.Methods where

import Effect (Effect)
import GoJS.Diagram.Types (class IsDiagram, InputEvent_)
import GoJS.Unsafe (callUnsafe0)

copy_ :: forall d. IsDiagram d => InputEvent_ d -> Effect (InputEvent_ d)
copy_ = callUnsafe0 "copy"
