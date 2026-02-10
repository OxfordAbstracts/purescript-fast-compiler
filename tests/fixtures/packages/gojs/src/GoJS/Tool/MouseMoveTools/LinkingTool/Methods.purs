module GoJS.Tool.MouseMoveTools.LinkingTool.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.GraphObject.Types (class IsGraphObject, class IsNode, Link_)
import GoJS.Tool.Types (LinkingTool_)
import GoJS.Unsafe (callUnsafe0, callUnsafe4)

doNoLink_ :: forall n g1 g2. IsNode n => IsGraphObject g1 => IsGraphObject g2 => n -> g1 -> n -> g2 -> LinkingTool_ -> Effect Unit
doNoLink_ = callUnsafe4 "doNoLink"

findLinkablePort_ :: forall @g.  LinkingTool_ -> Effect (Maybe g)
findLinkablePort_ t = toMaybe <$> callUnsafe0 "findLinkablePort" t

insertLink_ :: forall n1 n2 g1 g2. IsNode n1 => IsGraphObject g1 => IsNode n2 => IsGraphObject g2 => n1 -> g1 -> n2 -> g2 -> LinkingTool_ -> Effect (Maybe Link_)
insertLink_ n1 g1 n2 g2 t = toMaybe <$> callUnsafe4 "insertLink" n1 g1 n2 g2 t
