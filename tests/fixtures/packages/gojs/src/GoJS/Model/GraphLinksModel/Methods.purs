module GoJS.Model.GraphLinksModel.Methods where

import Prelude

import Effect (Effect)
import GoJS.Key (Key(..), toKey, undefinedk)
import GoJS.Model.Types (GraphLinksModel_)
import GoJS.Unsafe (callUnsafe1, callUnsafe2)

addLabelKeyForLinkData_ :: forall nodeData linkData. Record linkData -> Key -> GraphLinksModel_ linkData nodeData -> Effect Unit
addLabelKeyForLinkData_ r = case _ of
  StringKey s -> callUnsafe2 "addLabelKeyForLinkData" r s
  NumberKey n -> callUnsafe2 "addLabelKeyForLinkData" r n
  UndefinedKey -> callUnsafe2 "addLabelKeyForLinkData" r undefinedk

addLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Unit
addLinkData_ = callUnsafe1 "addLinkData"

containsLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Boolean
containsLinkData_ = callUnsafe1 "containsLinkData"

copyLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect (Record linkData)
copyLinkData_ = callUnsafe1 "copyLinkData"

findLinkDataForKey_ :: forall nodeData linkData. Key -> GraphLinksModel_ linkData nodeData -> Effect (Record linkData)
findLinkDataForKey_ = case _ of
  StringKey s -> callUnsafe1 "findLinkDataForKey" s
  NumberKey n -> callUnsafe1 "findLinkDataForKey" n
  UndefinedKey -> callUnsafe1 "findLinkDataForKey" undefinedk

getCategoryForLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect String
getCategoryForLinkData_ = callUnsafe1 "getCategoryForLinkData"

getFromKeyForLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Key
getFromKeyForLinkData_ r m = toKey <$> callUnsafe1 "getFromKeyForLinkData" r m

getFromPortIdForLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect String
getFromPortIdForLinkData_ = callUnsafe1 "getFromPortIdForLinkData"

getGroupKeyForNodeData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Key
getGroupKeyForNodeData_ r m = toKey <$> callUnsafe1 "getGroupKeyForNodeData" r m

getKeyForLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Key
getKeyForLinkData_ r m = toKey <$> callUnsafe1 "getKeyForLinkData" r m

getToKeyForLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Key
getToKeyForLinkData_ r m = toKey <$> callUnsafe1 "getToKeyForLinkData" r m

getToPortIdForLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect String
getToPortIdForLinkData_ = callUnsafe1 "getToPortIdForLinkData"

isGroupForNodeData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Boolean
isGroupForNodeData_ = callUnsafe1 "isGroupForNodeData"

makeLinkDataKeyUnique_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Unit
makeLinkDataKeyUnique_ = callUnsafe1 "makeLinkDataKeyUnique"

removeLabelKeyForLinkData_ :: forall nodeData linkData. Record linkData -> Key -> GraphLinksModel_ linkData nodeData -> Effect Unit
removeLabelKeyForLinkData_ r = case _ of
  StringKey s -> callUnsafe2 "removeLabelKeyForLinkData" r s
  NumberKey n -> callUnsafe2 "removeLabelKeyForLinkData" r n
  UndefinedKey -> callUnsafe2 "removeLabelKeyForLinkData" r undefinedk

removeLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect Unit
removeLinkData_ = callUnsafe1 "removeLinkData"

setCategoryForLinkData_ :: forall nodeData linkData. Record linkData -> String -> GraphLinksModel_ linkData nodeData -> Effect Unit
setCategoryForLinkData_ = callUnsafe2 "setCategoryForLinkData"

setFromKeyForLinkData_ :: forall nodeData linkData. Record linkData -> Key -> GraphLinksModel_ linkData nodeData -> Effect Unit
setFromKeyForLinkData_ r = case _ of
  StringKey s -> callUnsafe2 "setFromKeyForLinkData" r s
  NumberKey n -> callUnsafe2 "setFromKeyForLinkData" r n
  UndefinedKey -> callUnsafe2 "setFromKeyForLinkData" r undefinedk

setFromPortIdForLinkData_ :: forall nodeData linkData. Record linkData -> String -> GraphLinksModel_ linkData nodeData -> Effect Unit
setFromPortIdForLinkData_ = callUnsafe2 "setFromPortIdForLinkData"

setGroupKeyForNodeData_ :: forall nodeData linkData. Record nodeData -> Key -> GraphLinksModel_ linkData nodeData -> Effect Unit
setGroupKeyForNodeData_ r = case _ of
  StringKey s -> callUnsafe2 "setGroupKeyForNodeData" r s
  NumberKey n -> callUnsafe2 "setGroupKeyForNodeData" r n
  UndefinedKey -> callUnsafe2 "setGroupKeyForNodeData" r undefinedk

setKeyForLinkData_ :: forall nodeData linkData. Record linkData -> Key -> GraphLinksModel_ linkData nodeData -> Effect Unit
setKeyForLinkData_ r = case _ of
  StringKey s -> callUnsafe2 "setKeyForLinkData" r s
  NumberKey n -> callUnsafe2 "setKeyForLinkData" r n
  UndefinedKey -> callUnsafe2 "setKeyForLinkData" r undefinedk

setToKeyForLinkData_ :: forall nodeData linkData. Record linkData -> Key -> GraphLinksModel_ linkData nodeData -> Effect Unit
setToKeyForLinkData_ r = case _ of
  StringKey s -> callUnsafe2 "setToKeyForLinkData" r s
  NumberKey n -> callUnsafe2 "setToKeyForLinkData" r n
  UndefinedKey -> callUnsafe2 "setToKeyForLinkData" r undefinedk

setToPortIdForLinkData_ :: forall nodeData linkData. Record linkData -> String -> GraphLinksModel_ linkData nodeData -> Effect Unit
setToPortIdForLinkData_ = callUnsafe2 "setToPortIdForLinkData"

addLinkDataCollection_ :: forall nodeData linkData. Array (Record linkData) -> GraphLinksModel_ linkData nodeData -> Effect Unit
addLinkDataCollection_ = callUnsafe1 "addLinkDataCollection"

getLabelKeysForLinkData_ :: forall nodeData linkData. Record linkData -> GraphLinksModel_ linkData nodeData -> Effect (Array Key)
getLabelKeysForLinkData_ r m = (toKey <$> _) <$> callUnsafe1 "getLabelKeysForLinkData" r m

mergeLinkDataArray_ :: forall nodeData linkData. Array (Record linkData) -> GraphLinksModel_ linkData nodeData -> Effect Unit
mergeLinkDataArray_ = callUnsafe1 "mergeLinkDataArray"

removeLinkDataCollection_ :: forall nodeData linkData. Array (Record linkData) -> GraphLinksModel_ linkData nodeData -> Effect Unit
removeLinkDataCollection_ = callUnsafe1 "removeLinkDataCollection"

setLabelKeysForLinkData_ :: forall nodeData linkData. Record linkData -> Array Key -> GraphLinksModel_ linkData nodeData -> Effect Unit
setLabelKeysForLinkData_ = callUnsafe2 "setLabelKeysForLinkData"
