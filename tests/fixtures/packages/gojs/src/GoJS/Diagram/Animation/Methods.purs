module GoJS.Diagram.Animation.Methods where

import Prelude

import Data.Variant (Variant, case_, on)
import Effect (Effect)
import GoJS.Diagram.Types (Animation_, class IsDiagram)
import GoJS.GraphObject.Types (class IsGraphObject, class IsPart)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2, callUnsafe5)
import Type.Prelude (Proxy(..))

add_ :: forall graphObject diagram startValue endValue. IsGraphObject graphObject => IsDiagram diagram => Variant (graphObject :: graphObject, diagram :: diagram) -> String -> startValue -> endValue -> Boolean -> Animation_ -> Effect Animation_
add_ animated prop startValue endValue isStyle animation = animated #
  ( case_
      # on (Proxy @"graphObject") (\graphObject -> callUnsafe5 "add" graphObject prop startValue endValue isStyle animation)
      # on (Proxy @"diagram") (\diagram -> callUnsafe5 "add" diagram prop startValue endValue isStyle animation)
  )

addTemporaryPart_ :: forall part diagram. IsPart part => IsDiagram diagram => part -> diagram -> Animation_ -> Effect Animation_
addTemporaryPart_ part diagramram = callUnsafe2 "addTemporaryPart" part diagramram

getTemporaryState_ :: forall graphObject diagram nodeData. IsGraphObject graphObject => IsDiagram diagram => Variant (graphObject :: graphObject, diagram :: diagram) -> Animation_ -> Effect (Record nodeData)
getTemporaryState_ animated animation = animated #
  ( case_
      # on (Proxy @"graphObject") (\graphObject -> callUnsafe1 "getTemporaryState" graphObject animation)
      # on (Proxy @"diagram") (\diagram -> callUnsafe1 "getTemporaryState" diagram animation)
  )

start_ :: Animation_ -> Effect Animation_
start_ = callUnsafe0 "start"

stop_ :: Animation_ -> Effect Animation_
stop_ = callUnsafe0 "stop"
