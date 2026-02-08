module GoJS.Layout.ForceDirectedLayout.Methods where

import Prelude

import Effect (Effect)
import GoJS.Layout.Types (ForceDirectedEdge_, ForceDirectedVertex_, ForceDirectedLayout_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2)

addComments_ :: ForceDirectedVertex_ -> ForceDirectedLayout_ -> Effect Unit
addComments_ = callUnsafe1 "addComments"

commitLinks_ :: ForceDirectedLayout_ -> Effect Unit
commitLinks_ = callUnsafe0 "commitLinks"

commitNodes_ :: ForceDirectedLayout_ -> Effect Unit
commitNodes_ = callUnsafe0 "commitNodes"

electricalCharge_ :: ForceDirectedVertex_ -> ForceDirectedLayout_ -> Effect Number
electricalCharge_ = callUnsafe1 "electricalCharge"

electricalFieldX_ :: Number -> Number -> ForceDirectedLayout_ -> Effect Number
electricalFieldX_ = callUnsafe2 "electricalFieldX"

electricalFieldY_ :: Number -> Number -> ForceDirectedLayout_ -> Effect Number
electricalFieldY_ = callUnsafe2 "electricalFieldY"

gravitationalFieldX_ :: Number -> Number -> ForceDirectedLayout_ -> Effect Number
gravitationalFieldX_ = callUnsafe2 "gravitationalFieldX"

gravitationalFieldY_ :: Number -> Number -> ForceDirectedLayout_ -> Effect Number
gravitationalFieldY_ = callUnsafe2 "gravitationalFieldY"

gravitationalMass_ :: ForceDirectedVertex_ -> ForceDirectedLayout_ -> Effect Number
gravitationalMass_ = callUnsafe1 "gravitationalMass"

isFixed_ :: ForceDirectedVertex_ -> ForceDirectedLayout_ -> Effect Boolean
isFixed_ = callUnsafe1 "isFixed"

moveFixedVertex_ :: ForceDirectedVertex_ -> ForceDirectedLayout_ -> Effect Unit
moveFixedVertex_ = callUnsafe1 "moveFixedVertex"

springLength_ :: ForceDirectedEdge_ -> ForceDirectedLayout_ -> Effect Number
springLength_ = callUnsafe1 "springLength"

springStiffness_ :: ForceDirectedEdge_ -> ForceDirectedLayout_ -> Effect Number
springStiffness_ = callUnsafe1 "springStiffness"

