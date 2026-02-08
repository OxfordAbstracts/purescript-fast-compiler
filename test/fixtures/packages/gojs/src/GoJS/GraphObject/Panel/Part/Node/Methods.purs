module GoJS.GraphObject.Panel.Part.Node.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.Collection (Iterator_, Set_)
import GoJS.Geometry.Types (Rect_)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, class IsPart, Link_, Node_, Part_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe3)

-- Optional parameters excluded: level: number
collapseTree_ :: forall n. IsNode n => n -> Effect Unit
collapseTree_ = callUnsafe0 "collapseTree"

-- Optional parameters excluded: level: number
expandTree_ :: forall n. IsNode n => n -> Effect Unit
expandTree_ = callUnsafe0 "expandTree"

findCommonTreeParent_ :: forall n1 n2 @n3. IsNode n1 => IsNode n2 => IsNode n3 => n1 -> n2 -> Effect (Maybe n3)
findCommonTreeParent_ n1 n2 = toMaybe <$> callUnsafe1 "findCommonTreeParent" n1 n2

findExternalTreeLinksConnected_ :: forall n. IsNode n => n -> Effect (Iterator_ Link_)
findExternalTreeLinksConnected_ = callUnsafe0 "findExternalTreeLinksConnected"

-- Optional parameters: pid: string, otherpid: string
findLinksBetween_ :: forall n. IsNode n => n -> String -> String -> n -> Effect (Iterator_ Link_)
findLinksBetween_ = callUnsafe3 "findLinksBetween"

-- Optional parameters: pid: string
findLinksConnected_ :: forall n. IsNode n => String -> n -> Effect (Iterator_ Link_)
findLinksConnected_ = callUnsafe1 "findLinksConnected"

-- Optional parameters excluded: pid: string
findLinksInto_ :: forall n. IsNode n => n -> Effect (Iterator_ Link_)
findLinksInto_ = callUnsafe0 "findLinksInto"

-- Optional parameters excluded: pid: string
findLinksOutOf_ :: forall n. IsNode n => n -> Effect (Iterator_ Link_)
findLinksOutOf_ = callUnsafe0 "findLinksOutOf"

-- Optional parameters: pid: string, otherpid: string
findLinksTo_ :: forall n1 n2. IsNode n1 => IsNode n2 => n1 -> String -> String -> n2 -> Effect (Iterator_ Link_)
findLinksTo_ = callUnsafe3 "findLinksTo"

-- Optional parameters: pid: string
findNodesConnected_ :: forall n1 @n2. IsNode n1 => IsNode n2 => String -> n1 -> Effect (Iterator_ Node_)
findNodesConnected_ = callUnsafe1 "findNodesConnected"

-- Optional parameters: pid: string
findNodesInto_ :: forall n1 @n2. IsNode n1 => IsNode n2 => String -> n1 -> Effect (Iterator_ Node_)
findNodesInto_ = callUnsafe1 "findNodesInto"

-- Optional parameters: pid: string
findNodesOutOf_ :: forall n1 @n2. IsNode n1 => IsNode n2 => String -> n1 -> Effect (Iterator_ Node_)
findNodesOutOf_ = callUnsafe1 "findNodesOutOf"

findPort_ :: forall n @g. IsNode n => IsGraphObject g => String -> n -> Effect (Maybe g)
findPort_ x n = toMaybe <$> callUnsafe1 "findPort" x n

findTreeChildrenLinks_ :: forall n. IsNode n => n -> Effect (Iterator_ Link_)
findTreeChildrenLinks_ = callUnsafe0 "findTreeChildrenLinks"

findTreeChildrenNodes_ :: forall n1 @n2. IsNode n1 => IsNode n2 => n1 -> Effect (Iterator_ Node_)
findTreeChildrenNodes_ = callUnsafe0 "findTreeChildrenNodes"

findTreeLevel_ :: forall n. IsNode n => n -> Effect Number
findTreeLevel_ = callUnsafe0 "findTreeLevel"

findTreeParentChain_ :: forall n @p. IsPart p => n -> Effect (Set_ p)
findTreeParentChain_ = callUnsafe0 "findTreeParentChain"

findTreeParentLink_ :: forall n. IsNode n => n -> Effect (Maybe Link_)
findTreeParentLink_ n = toMaybe <$> callUnsafe0 "findTreeParentLink" n

findTreeParentNode_ :: forall n1 @n2. IsNode n1 => IsNode n2 => n1 -> Effect (Maybe n2)
findTreeParentNode_ n = toMaybe <$> callUnsafe0 "findTreeParentNode" n

-- Optional parameters excluded: level: number
findTreeParts_ :: forall n. IsNode n => n -> Effect (Set_ Part_)
findTreeParts_ = callUnsafe0 "findTreeParts"

findTreeRoot_ :: forall @n. IsNode n => n -> Effect n
findTreeRoot_ = callUnsafe0 "findTreeRoot"

findVisibleNode_ :: forall @n. IsNode n => n -> Effect n
findVisibleNode_ = callUnsafe0 "findVisibleNode"

getAvoidableRect_ :: forall n. IsNode n => Rect_ -> n -> Effect Rect_
getAvoidableRect_ = callUnsafe1 "getAvoidableRect"

isInTreeOf_ :: forall n1 n2. IsNode n1 => IsNode n2 => n1 -> n2 -> Effect Boolean
isInTreeOf_ = callUnsafe1 "isInTreeOf"
