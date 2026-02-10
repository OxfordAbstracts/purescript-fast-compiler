module GoJS.Tool.MouseDownTools.RelinkingTool.Methods where

import Prelude

import Effect (Effect)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, class IsPart, Link_)
import GoJS.Tool.Types (RelinkingTool_)
import GoJS.Unsafe (callUnsafe2, callUnsafe4)

reconnectLink_ :: forall g n p. IsGraphObject g => IsNode n => IsPart p => Link_ -> n -> g -> Boolean -> RelinkingTool_ -> Effect Boolean
reconnectLink_ = callUnsafe4 "reconnectLink"

doNoRelink_ :: forall g n. IsGraphObject g => IsNode n => Link_ -> n -> g -> Boolean -> RelinkingTool_ -> Effect Boolean
doNoRelink_ = callUnsafe4 "doNoRelink"

copyLinkProperties_ :: forall l. Link_ -> l -> RelinkingTool_ -> Effect Unit
copyLinkProperties_ = callUnsafe2 "copyLinkProperties"