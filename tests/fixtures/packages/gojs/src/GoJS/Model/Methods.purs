module GoJS.Model.Methods where

import Prelude

import Data.Variant (Variant, case_, on)
import Effect (Effect)
import Effect.Uncurried (EffectFn1)
import GoJS.EnumValue (EnumValue_)
import GoJS.Key (Key(..), undefinedk)
import GoJS.Model.Types (class IsModel, ChangedEvent_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2, callUnsafe3, callUnsafe4, callUnsafe5)
import Type.Prelude (Proxy(..))

addChangedListener_ :: forall m nodeData. IsModel (m nodeData) => EffectFn1 ChangedEvent_ Unit -> m nodeData -> Effect (m nodeData)
addChangedListener_ = callUnsafe1 "addChangedListener"

addNodeData_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> m nodeData -> Effect Unit
addNodeData_ = callUnsafe1 "addNodeData"

addNodeDataCollection_ :: forall m nodeData. IsModel (m nodeData) => Array (Record nodeData) -> m nodeData -> Effect Unit
addNodeDataCollection_ = callUnsafe1 "addNodeDataCollection"

applyIncrementalJson_ :: forall m nodeData. IsModel (m nodeData) => Variant (string :: String, objectData :: nodeData) -> m nodeData -> Effect Unit
applyIncrementalJson_ incremental model = incremental #
  ( case_
      # on (Proxy @"string") (\string -> callUnsafe1 "applyIncrementalJson" string model)
      # on (Proxy @"objectData") (\objectData -> callUnsafe1 "applyIncrementalJson" objectData model)
  )

assignAllDataProperties_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> Record nodeData -> m nodeData -> Effect Unit
assignAllDataProperties_ = callUnsafe2 "assignAllDataProperties"

clear_ :: forall m nodeData. IsModel (m nodeData) => m nodeData -> Effect Unit
clear_ = callUnsafe0 "clear"

cloneDeep_ :: forall m nodeData. IsModel (m nodeData) => m nodeData -> Effect (m nodeData)
cloneDeep_ = callUnsafe0 "cloneDeep"

-- Related to overriding and extensions.
cloneProtected_ :: forall m nodeData. IsModel (m nodeData) => m nodeData -> Effect Unit
cloneProtected_ = callUnsafe0 "cloneProtected"

-- Optional parameters: tname: string
commit_ :: forall m nodeData. IsModel (m nodeData) => (EffectFn1 (m nodeData) Unit) -> String -> m nodeData -> Effect Unit
commit_ = callUnsafe2 "commit"

commitTransaction_ :: forall m nodeData. IsModel (m nodeData) => String -> m nodeData -> Effect Boolean
commitTransaction_ = callUnsafe1 "commitTransaction"

containsNodeData_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> m nodeData -> Effect Boolean
containsNodeData_ = callUnsafe1 "containsNodeData"

copy_ :: forall m nodeData. IsModel (m nodeData) => m nodeData -> Effect (m nodeData)
copy_ = callUnsafe0 "copy"

copyNodeData_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> m nodeData -> Effect (Record nodeData)
copyNodeData_ = callUnsafe1 "copyNodeData"

findNodeDataForKey_ :: forall m nodeData. IsModel (m nodeData) => Key -> m nodeData  -> Effect (Record nodeData)
findNodeDataForKey_ = case _ of
  StringKey s -> callUnsafe1 "findNodeDataForKey" s
  NumberKey n -> callUnsafe1 "findNodeDataForKey" n
  UndefinedKey -> callUnsafe1 "findNodeDataForKey" undefinedk

getCategoryForNodeData_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> m nodeData -> Effect String
getCategoryForNodeData_ = callUnsafe1 "getCategoryForNodeData"

getKeyForNodeData_ :: forall m nodeData. Record nodeData -> m -> Effect Key
getKeyForNodeData_ = callUnsafe1 "getKeyForNodeData"

makeNodeDataKeyUnique_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> m nodeData -> Effect Unit
makeNodeDataKeyUnique_ = callUnsafe1 "makeNodeDataKeyUnique"

mergeNodeDataArray_ :: forall m nodeData. IsModel (m nodeData) => Array (Record nodeData) -> m nodeData -> Effect Unit
mergeNodeDataArray_ = callUnsafe1 "mergeNodeDataArray"

raiseChangedEvent_ :: forall m nodeData oldval newval. IsModel (m nodeData) => EnumValue_ -> String -> Record nodeData -> oldval -> newval -> m nodeData -> Effect Unit
raiseChangedEvent_ = callUnsafe5 "raiseChangedEvent"

raiseDataChanged_ :: forall m nodeData oldval newval. IsModel (m nodeData) => Record nodeData -> String -> oldval -> newval -> m nodeData -> Effect Unit
raiseDataChanged_ = callUnsafe4 "raiseDataChanged"

removeChangedListener_ :: forall m nodeData. IsModel (m nodeData) => EffectFn1 ChangedEvent_ Unit -> m nodeData -> Effect Unit
removeChangedListener_ = callUnsafe1 "removeChangedListener"

removeNodeData_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> m nodeData -> Effect Unit
removeNodeData_ = callUnsafe1 "removeNodeData"

removeNodeDataCollection_ :: forall m nodeData. IsModel (m nodeData) => Array (Record nodeData) -> m nodeData -> Effect Unit
removeNodeDataCollection_ = callUnsafe1 "removeNodeDataCollection"

rollbackTransaction_ :: forall m nodeData. IsModel (m nodeData) => m nodeData -> Effect Boolean
rollbackTransaction_ = callUnsafe0 "rollbackTransaction"

setCategoryForNodeData_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> String -> m nodeData -> Effect Unit
setCategoryForNodeData_ = callUnsafe2 "setCategoryForNodeData"

setDataProperty_ :: forall m nodeData prop. IsModel (m nodeData) => Record nodeData -> String -> prop -> m nodeData -> Effect Unit
setDataProperty_ = callUnsafe3 "setDataProperty"

setKeyForNodeData_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> Key -> m nodeData -> Effect Unit
setKeyForNodeData_ m = case _ of
  StringKey s -> callUnsafe2 "setKeyForNodeData" m s
  NumberKey n -> callUnsafe2 "setKeyForNodeData" m n
  UndefinedKey -> callUnsafe2 "setKeyForNodeData" m undefinedk

startTransaction_ :: forall m nodeData. IsModel (m nodeData) => String -> m nodeData -> Effect Boolean
startTransaction_ = callUnsafe1 "startTransaction"

toJson_ :: forall m. IsModel m => m -> Effect String
toJson_ = callUnsafe0 "toJson"

updateTargetBindings_ :: forall m nodeData. IsModel (m nodeData) => Record nodeData -> String -> m nodeData -> Effect Unit
updateTargetBindings_ = callUnsafe2 "updateTargetBindings"

-- TODO: Implement IncrementalData and related methods: toIncrementalData, toIncrementalJson
-- TODO: Item-related methods are not supported yet: addArrayItem, removeArrayItem, insertArrayItem
