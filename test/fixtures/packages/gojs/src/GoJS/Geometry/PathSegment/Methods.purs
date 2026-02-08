module GoJS.Geometry.PathSegment.Methods where

import Effect (Effect)
import GoJS.Geometry.Types (PathSegment_)
import GoJS.Unsafe (callUnsafe0)

close_ :: PathSegment_ -> Effect PathSegment_
close_ = callUnsafe0 "close"

copy_ :: PathSegment_ -> Effect PathSegment_
copy_ = callUnsafe0 "copy"

