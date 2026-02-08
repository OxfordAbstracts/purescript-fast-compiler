module GoJS.Diagram.Layout.Methods where

import Prelude

import Data.Variant (Variant, case_, on)
import Effect (Effect)
import GoJS.Collection (Iterator_, Set_)
import GoJS.Diagram.Types (class IsDiagram)
import GoJS.Geometry.Types (Point_, Rect_)
import GoJS.GraphObject.Types (class IsPart, Group_, Part_)
import GoJS.Layout.Types (class IsLayout, class LayoutNetwork)
import GoJS.Unsafe (callUnsafe0, callUnsafe1)
import Type.Proxy (Proxy(..))

collectParts_ :: forall d l. IsLayout l => IsDiagram d => d -> l -> Effect (Set_ Part_)
collectParts_ = callUnsafe1 "collectParts"

commitLayout_ :: forall l. IsLayout l => l -> Effect Unit
commitLayout_ = callUnsafe0 "commitLayout"

copy_ :: forall l. IsLayout l => l -> Effect l
copy_ = callUnsafe0 "copy"

-- GridLayout does not use networks, so does not have an instance of LayoutNetwork
-- and therefore this method should not be called for it. A specification of this function's
-- type like this will not compile:
-- x :: forall n. GridLayout_ -> Effect n
-- x = createNetwork_
-- The same goes for makeNetwork.

createNetwork_ :: forall l n _e _v. LayoutNetwork l n _e _v => l -> Effect n
createNetwork_ = callUnsafe0 "createNetwork"

makeNetwork_ :: forall l n _e _v d. IsDiagram d => LayoutNetwork l n _e _v => Variant (diagram :: d, parts :: Iterator_ Part_, group :: Group_) -> l -> Effect n
makeNetwork_ coll layout = coll #
  ( case_
      # on (Proxy @"diagram") (\diagram -> callUnsafe1 "makeNetwork" diagram layout)
      # on (Proxy @"parts") (\parts -> callUnsafe1 "makeNetwork" parts layout)
      # on (Proxy @"group") (\group -> callUnsafe1 "makeNetwork" group layout)
  )

doLayout_ :: forall l d. IsLayout l => Variant (diagram :: d, parts :: Iterator_ Part_, group :: Group_) -> l -> Effect Unit
doLayout_ coll layout = coll #
  ( case_
      # on (Proxy @"diagram") (\diagram -> callUnsafe1 "doLayout" diagram layout)
      # on (Proxy @"parts") (\parts -> callUnsafe1 "doLayout" parts layout)
      # on (Proxy @"group") (\group -> callUnsafe1 "doLayout" group layout)
  )

-- Optional arguments excluded: rect: Rect
getLayoutBounds_ :: forall p l. IsLayout l => IsPart p => p -> l -> Effect Rect_
getLayoutBounds_ = callUnsafe1 "getLayoutBounds"

initialOrigin_ :: forall l. IsLayout l => Point_ -> l -> Effect Point_
initialOrigin_ = callUnsafe1 "initialOrigin"

invalidateLayout_ :: forall l. IsLayout l => l -> Effect Unit
invalidateLayout_ = callUnsafe0 "invalidateLayout"

updateParts_ :: forall l. IsLayout l => l -> Effect Unit
updateParts_ = callUnsafe0 "updateParts"
