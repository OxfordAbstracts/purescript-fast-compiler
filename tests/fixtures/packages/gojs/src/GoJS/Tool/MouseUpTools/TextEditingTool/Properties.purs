module GoJS.Tool.MouseUpTools.TextEditingTool.Properties where

import Prelude

import Data.Function.Uncurried (Fn3)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import GoJS.EnumValue (EnumValue_)
import GoJS.GraphObject.Types (TextBlock_)
import GoJS.Tool.Types (HTMLInfo_, TextEditingTool_)
import GoJS.Unsafe (getUnsafe)

_currentTextEditor :: TextEditingTool_ -> HTMLInfo_
_currentTextEditor = getUnsafe ["currentTextEditor"]

_defaultTextEditor :: TextEditingTool_ -> HTMLInfo_
_defaultTextEditor = getUnsafe ["defaultTextEditor"]

_selectsTextOnActivate :: TextEditingTool_ -> Boolean
_selectsTextOnActivate = getUnsafe ["selectsTextOnActivate"]

_starting :: TextEditingTool_ -> EnumValue_
_starting = getUnsafe ["starting"]

_state :: TextEditingTool_ -> EnumValue_
_state = getUnsafe ["state"]

_textBlock :: TextEditingTool_ -> TextBlock_
_textBlock = getUnsafe ["textBlock"]

_textValidation :: TextEditingTool_ -> Maybe (Fn3 TextBlock_ String String Boolean)
_textValidation = toMaybe <<< getUnsafe ["textValidation"]