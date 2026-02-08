module GoJS.Diagram.AnimationTrigger.Methods where


import Effect (Effect)
import GoJS.Diagram.Types (AnimationTrigger_)
import GoJS.Unsafe (callUnsafe0)

copy_ :: AnimationTrigger_ -> Effect AnimationTrigger_
copy_ = callUnsafe0 "copy"
