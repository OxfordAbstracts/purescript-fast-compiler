module GoJS.Diagram.CommandHandler.Properties where

import Data.Function.Uncurried (Fn2)
import GoJS.Diagram.Types (Diagram_)
import GoJS.GraphObject.Types (Group_, Part_)
import GoJS.Diagram.CommandHandler.Types (CommandHandler_)
import GoJS.Unsafe (getUnsafe)

_archetypeGroupData :: forall nodeData. CommandHandler_ -> Record nodeData
_archetypeGroupData = getUnsafe ["archetypeGroupData"]

_copiesConnectedLinks :: CommandHandler_ -> Boolean
_copiesConnectedLinks = getUnsafe ["copiesConnectedLinks"]

_copiesGroupKey :: CommandHandler_ -> Boolean
_copiesGroupKey = getUnsafe ["copiesGroupKey"]

_copiesParentKey :: CommandHandler_ -> Boolean
_copiesParentKey = getUnsafe ["copiesParentKey"]

_copiesTree :: CommandHandler_ -> Boolean
_copiesTree = getUnsafe ["copiesTree"]

_deletesTree :: CommandHandler_ -> Boolean
_deletesTree = getUnsafe ["deletesTree"]

_deletesConnectedLinks :: CommandHandler_ -> Boolean
_deletesConnectedLinks = getUnsafe ["deletesConnectedLinks"]

-- Read-only
_diagram :: CommandHandler_ -> Diagram_
_diagram = getUnsafe ["diagram"]

_isZoomToFitRestoreEnabled :: CommandHandler_ -> Boolean
_isZoomToFitRestoreEnabled = getUnsafe ["isZoomToFitRestoreEnabled"]

_memberValidation :: CommandHandler_ -> Fn2 Group_ Part_ Boolean
_memberValidation = getUnsafe ["memberValidation"]

_zoomFactor :: CommandHandler_ -> Number
_zoomFactor = getUnsafe ["zoomFactor"]

