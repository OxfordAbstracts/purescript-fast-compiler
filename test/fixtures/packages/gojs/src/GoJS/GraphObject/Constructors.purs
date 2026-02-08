module GoJS.GraphObject.Constructors where

import Effect (Effect)
import GoJS.GraphObject.Types (Shape_, Placeholder_, TextBlock_, Picture_, Panel_, Part_, Node_, Group_, Link_, Adornment_, Button_)
import GoJS.Unsafe (constructor0, constructor1)

newShape :: String -> Effect Shape_
newShape = constructor1 "Shape"

newPlaceholder :: Effect Placeholder_
newPlaceholder = constructor0 "Placeholder"

newTextBlock :: String -> Effect TextBlock_
newTextBlock = constructor1 "TextBlock"

newPicture :: String -> Effect Picture_
newPicture = constructor1 "Picture"

newPanel :: String -> Effect Panel_
newPanel = constructor1 "Panel"

newPart :: String -> Effect Part_
newPart = constructor1 "Part"

newNode :: String -> Effect Node_
newNode = constructor1 "Node"

newGroup :: String -> Effect Group_
newGroup = constructor1 "Group"

newLink :: Effect Link_
newLink = constructor0 "Link"

newAdornment :: String -> Effect Adornment_
newAdornment = constructor1 "Adornment"

-- Buttons and ContextMenus are a special case which use `make`. Should be obsoleted in GoJS 3.0
foreign import newButton :: String -> String -> Effect Button_
foreign import newContextMenu :: Effect Adornment_
foreign import newToolTip :: Effect Adornment_