module GoJS.Model.TreeModel.Methods where

import Prelude

import Effect (Effect)
import GoJS.Key (Key(..), toKey, undefinedk)
import GoJS.Model.Types (TreeModel_)
import GoJS.Unsafe (callUnsafe1, callUnsafe2)

getParentKeyForNodeData_ :: forall nodeData. Record nodeData -> TreeModel_ nodeData -> Effect Key
getParentKeyForNodeData_ r m = toKey <$> callUnsafe1 "getParentKeyForNodeData" r m

getParentLinkCategoryForNodeData_ :: forall nodeData. Record nodeData -> TreeModel_ nodeData -> Effect Key
getParentLinkCategoryForNodeData_ r m = toKey <$> callUnsafe1 "getParentLinkCategoryForNodeData" r m

setParentKeyForNodeData_ :: forall nodeData. Record nodeData -> Key -> TreeModel_ nodeData -> Effect Unit
setParentKeyForNodeData_ r = case _ of
    StringKey s -> callUnsafe2 "setParentKeyForNodeData" r s
    NumberKey n -> callUnsafe2 "setParentKeyForNodeData" r n
    UndefinedKey -> callUnsafe2 "setParentKeyForNodeData" r undefinedk

setParentLinkCategoryForNodeData_ :: forall nodeData. Record nodeData -> String -> TreeModel_ nodeData -> Effect Unit
setParentLinkCategoryForNodeData_ = callUnsafe2 "setParentLinkCategoryForNodeData"
