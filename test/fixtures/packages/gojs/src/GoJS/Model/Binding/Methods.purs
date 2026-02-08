module GoJS.Model.Binding.Methods where

import Effect (Effect)
import GoJS.Model.Types (Binding_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)

ofModel_ :: Binding_ -> Effect Binding_
ofModel_ = callUnsafe0 "ofModel"

-- Optional arguments excluded: srcname: string
ofObject_ :: Binding_ -> Effect Binding_
ofObject_ = callUnsafe0 "ofObject"

-- Optional arguments: backconv: (val: any, sourceData: any, model: Model) => any. Here we treat it as just any -> any.
makeTwoWay_ :: forall from to. (from -> to) -> Binding_ -> Effect Binding_
makeTwoWay_ = callUnsafe1 "makeTwoWay"