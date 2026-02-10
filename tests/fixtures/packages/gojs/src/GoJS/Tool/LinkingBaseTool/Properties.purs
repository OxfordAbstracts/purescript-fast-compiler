module GoJS.Tool.LinkingBaseTool.Properties where

import Prelude

import Effect.Uncurried (EffectFn5)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, Link_)
import GoJS.Tool.LinkingBaseTool.Types (class IsLinkingBaseTool)
import GoJS.Unsafe.Get (getUnsafe)


_isForwards :: forall t. IsLinkingBaseTool t => t -> Boolean
_isForwards = getUnsafe ["isForwards"]

_isUnconnectedLinkValid :: forall t. IsLinkingBaseTool t => t -> Boolean
_isUnconnectedLinkValid = getUnsafe ["isUnconnectedLinkValid"]

_linkValidation :: forall t n1 p1 n2 p2. IsLinkingBaseTool t => IsNode n1 => IsGraphObject p1 => IsNode n2 => IsGraphObject p2 => t -> EffectFn5 n1 p1 n2 p2 Link_ Boolean
_linkValidation = getUnsafe ["linkValidation"]

_linkingCursor :: forall t. IsLinkingBaseTool t => t -> String
_linkingCursor = getUnsafe ["linkingCursor"]

_originalFromNode :: forall t @n. IsLinkingBaseTool t => IsNode n => t -> n
_originalFromNode = getUnsafe ["originalFromNode"]

_originalFromPort :: forall t @p. IsLinkingBaseTool t => IsGraphObject p => t -> p
_originalFromPort = getUnsafe ["originalFromPort"]

_originalLink :: forall t. IsLinkingBaseTool t => t -> Link_
_originalLink = getUnsafe ["originalLink"]

_originalToNode :: forall t @n. IsLinkingBaseTool t => IsNode n => t -> n
_originalToNode = getUnsafe ["originalToNode"]

_originalToPort :: forall t @p. IsLinkingBaseTool t => IsGraphObject p => t -> p
_originalToPort = getUnsafe ["originalToPort"]

_portGravity :: forall t. IsLinkingBaseTool t => t -> Number
_portGravity = getUnsafe ["portGravity"]

_portTargeted :: forall t n1 p1 n2 p2. IsLinkingBaseTool t => IsNode n1 => IsGraphObject p1 => IsNode n2 => IsGraphObject p2 => t -> EffectFn5 n1 p1 n2 p2 Boolean Unit
_portTargeted = getUnsafe ["portTargeted"]

_targetPort :: forall t @p. IsLinkingBaseTool t => IsGraphObject p => t -> p
_targetPort = getUnsafe ["targetPort"]

_temporaryFromNode :: forall t @n. IsLinkingBaseTool t => IsNode n => t -> n
_temporaryFromNode = getUnsafe ["temporaryFromNode"]

_temporaryFromPort :: forall t @p. IsLinkingBaseTool t => IsGraphObject p => t -> p
_temporaryFromPort = getUnsafe ["temporaryFromPort"]

_temporaryLink :: forall t. IsLinkingBaseTool t => t -> Link_
_temporaryLink = getUnsafe ["temporaryLink"]

_temporaryToNode :: forall t @n. IsLinkingBaseTool t => IsNode n => t -> n
_temporaryToNode = getUnsafe ["temporaryToNode"]

_temporaryToPort :: forall t @p. IsLinkingBaseTool t => IsGraphObject p => t -> p
_temporaryToPort = getUnsafe ["temporaryToPort"]