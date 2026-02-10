module GoJS.Model.TreeModel.Properties where

import Prelude

import GoJS.Key (Key, KeyProperty, toKeyProperty)
import GoJS.Model.Types (TreeModel_)
import GoJS.Unsafe (getUnsafe)

_nodeParentKeyProperty :: forall nodeData. TreeModel_ nodeData -> KeyProperty nodeData Key
_nodeParentKeyProperty = toKeyProperty <<< getUnsafe [ "nodeParentKeyProperty" ]

_parentLinkCategoryProperty :: forall nodeData. TreeModel_ nodeData -> KeyProperty nodeData String
_parentLinkCategoryProperty = toKeyProperty <<< getUnsafe [ "parentLinkCategoryProperty" ]
