module GoJS.Tool.LinkingBaseTool.Methods where

import Prelude


import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode)
import GoJS.Tool.LinkingBaseTool.Types (class IsLinkingBaseTool)
import GoJS.Unsafe (callUnsafe1, callUnsafe2, callUnsafe3, callUnsafe4, callUnsafe5)

-- Methods from LinkingBaseTool:
copyPortProperties_ :: forall n1 g1 n2 g2 t. IsLinkingBaseTool t => IsNode n1 => IsGraphObject g1 => IsNode n2 => IsGraphObject g2 => Boolean -> n1 -> g1 -> n2 -> g2 -> t -> Effect Unit
copyPortProperties_ = callUnsafe5 "copyPortProperties"

findTargetPort_ :: forall @g t. IsLinkingBaseTool t => IsGraphObject g => Boolean -> t -> Effect (Maybe g)
findTargetPort_ b t = toMaybe <$> callUnsafe1 "findTargetPort" b t

isInSameNode_ :: forall g1 g2 t. IsLinkingBaseTool t => IsGraphObject g1 => IsGraphObject g2 => g1 -> g2 -> t -> Effect Boolean
isInSameNode_ = callUnsafe2 "isInSameNode"

isLinked_ :: forall g1 g2 t. IsLinkingBaseTool t => IsGraphObject g1 => IsGraphObject g2 => g1 -> g2 -> t -> Effect Boolean
isLinked_ = callUnsafe2 "isLinked"

-- Optional parameters excluded: ignore: Link
isValidCycle_ :: forall n1 n2 t. IsLinkingBaseTool t => IsNode n1 => IsNode n2 => n1 -> n2 -> t -> Effect Boolean
isValidCycle_ = callUnsafe2 "isValidCycle"

isValidFrom_ :: forall n g t. IsLinkingBaseTool t => IsNode n => IsGraphObject g => n -> g -> t -> Effect Boolean
isValidFrom_ = callUnsafe2 "isValidFrom"

isValidLink_ :: forall n1 g1 n2 g2 t. IsLinkingBaseTool t => IsNode n1 => IsGraphObject g1 => IsNode n2 => IsGraphObject g2 => n1 -> g1 -> n2 -> g2 -> t -> Effect Boolean
isValidLink_ = callUnsafe4 "isValidLink"

isValidTo_ :: forall n g t. IsLinkingBaseTool t => IsNode n => IsGraphObject g => n -> g -> t -> Effect Boolean
isValidTo_ = callUnsafe2 "isValidTo"

setNoTargetPortProperties_ :: forall n g t. IsLinkingBaseTool t => IsNode n => IsGraphObject g => n -> g -> Boolean -> t -> Effect Unit
setNoTargetPortProperties_ = callUnsafe3 "setNoTargetPortProperties"