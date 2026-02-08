module GoJS.Model.GraphLinksModel.Properties where

import Prelude

import Effect.Uncurried (EffectFn2, mkEffectFn2, runEffectFn2)
import GoJS.Key (Key, KeyProperty, toKey, toKeyProperty)
import GoJS.Model.Types (GraphLinksModel_)
import GoJS.Unsafe (getUnsafe)

_archetypeNodeData :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> Record nodeData
_archetypeNodeData = getUnsafe [ "archetypeNodeData" ]

_copyLinkDataFunction :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> EffectFn2 (Record linkData) (GraphLinksModel_ linkData linkData) (Record linkData)
_copyLinkDataFunction = getUnsafe [ "copyLinkDataFunction" ]

_linkCategoryProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty linkData String
_linkCategoryProperty = toKeyProperty <<< getUnsafe [ "linkCategoryProperty" ]

_linkDataArray :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> Array (Record linkData)
_linkDataArray = getUnsafe [ "linkDataArray" ]

_linkFromKeyProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty linkData Key
_linkFromKeyProperty = toKeyProperty <<< getUnsafe [ "linkFromKeyProperty" ]

_linkFromPortIdProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty linkData String
_linkFromPortIdProperty = toKeyProperty <<< getUnsafe [ "linkFromPortIdProperty" ]

_linkKeyProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty linkData Key
_linkKeyProperty = toKeyProperty <<< getUnsafe [ "linkKeyProperty" ]

_linkLabelKeysProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty linkData (Array Key)
_linkLabelKeysProperty = toKeyProperty <<< getUnsafe [ "linkLabelKeysProperty" ]

_linkToKeyProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty linkData Key
_linkToKeyProperty = getUnsafe [ "linkToKeyProperty" ]

_linkToPortIdProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty linkData String
_linkToPortIdProperty = getUnsafe [ "linkToPortIdProperty" ]

_makeUniqueLinkKeyFunction :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> EffectFn2 (Record linkData) (GraphLinksModel_ linkData linkData) Key
_makeUniqueLinkKeyFunction m = mkEffectFn2 $ \a b -> do -- Remake the effectful function since we need to transform the return js value into a Key
    let f = getUnsafe [ "makeUniqueLinkKeyFunction" ] m
    res <- runEffectFn2 f a b
    pure $ toKey res

_nodeGroupKeyProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty nodeData Key
_nodeGroupKeyProperty = toKeyProperty <<< getUnsafe [ "nodeGroupKeyProperty" ]

_nodeIsGroupProperty :: forall nodeData linkData. GraphLinksModel_ nodeData linkData -> KeyProperty nodeData Boolean
_nodeIsGroupProperty = toKeyProperty <<< getUnsafe [ "nodeIsGroupProperty" ]
