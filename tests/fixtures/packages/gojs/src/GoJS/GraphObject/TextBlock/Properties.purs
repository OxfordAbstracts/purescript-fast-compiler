module GoJS.GraphObject.TextBlock.Properties where

import Prelude

import Data.Function.Uncurried (Fn2, Fn3)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn3)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Spot_)
import GoJS.GraphObject.Types (TextBlock_)
import GoJS.Tool (HTMLInfo_)
import GoJS.Unsafe (getUnsafe)

_choices :: TextBlock_ -> Array String
_choices = getUnsafe [ "choices" ]

_editable :: TextBlock_ -> Boolean
_editable = getUnsafe [ "editable" ]

_errorFunction :: TextBlock_ -> Maybe (EffectFn3 TextBlock_ String String Unit)
_errorFunction = toMaybe <<< getUnsafe [ "errorFunction" ]

_flip :: TextBlock_ -> EnumValue_
_flip = getUnsafe [ "flip" ]

_font :: TextBlock_ -> String
_font = getUnsafe [ "font" ]

_formatting :: TextBlock_ -> EnumValue_
_formatting = getUnsafe [ "formatting" ]

_graduatedEnd :: TextBlock_ -> Number
_graduatedEnd = getUnsafe [ "graduatedEnd" ]

_graduatedFunction :: TextBlock_ -> Maybe (Fn2 Number TextBlock_ Number)
_graduatedFunction = toMaybe <<< getUnsafe [ "graduatedFunction" ]

_graduatedStart :: TextBlock_ -> Number
_graduatedStart = getUnsafe [ "graduatedStart" ]

_graduatedSkip :: TextBlock_ -> Maybe (Fn2 Number TextBlock_ Boolean)
_graduatedSkip = toMaybe <<< getUnsafe [ "graduatedSkip" ]

_interval :: TextBlock_ -> Number
_interval = getUnsafe [ "interval" ]

_isMultiline :: TextBlock_ -> Boolean
_isMultiline = getUnsafe [ "isMultiline" ]

-- Read-only
_isOverflowed :: TextBlock_ -> Boolean
_isOverflowed = getUnsafe [ "isOverflowed" ]

_isStrikethrough :: TextBlock_ -> Boolean
_isStrikethrough = getUnsafe [ "isStrikethrough" ]

_isUnderline :: TextBlock_ -> Boolean
_isUnderline = getUnsafe [ "isUnderline" ]

-- Read-only
_lineCount :: TextBlock_ -> Number
_lineCount = getUnsafe [ "lineCount" ]

-- Read-only
_lineHeight :: TextBlock_ -> Number
_lineHeight = getUnsafe [ "lineHeight" ]

_maxLines :: TextBlock_ -> Number
_maxLines = getUnsafe [ "maxLines" ]

_overflow :: TextBlock_ -> EnumValue_
_overflow = getUnsafe [ "overflow" ]

_spacingAbove :: TextBlock_ -> Number
_spacingAbove = getUnsafe [ "spacingAbove" ]

_spacingBelow :: TextBlock_ -> Number
_spacingBelow = getUnsafe [ "spacingBelow" ]

_stroke :: TextBlock_ -> String
_stroke = getUnsafe [ "stroke" ]

_text :: TextBlock_ -> String
_text = getUnsafe [ "text" ]

_textAlign :: TextBlock_ -> String
_textAlign = getUnsafe [ "textAlign" ]

_textEdited :: TextBlock_ -> Maybe (EffectFn3 TextBlock_ String String Unit)
_textEdited = toMaybe <<< getUnsafe [ "textEdited" ]

_textEditor :: TextBlock_ -> Maybe HTMLInfo_
_textEditor = toMaybe <<< getUnsafe [ "textEditor" ]

_textValidation :: TextBlock_ -> Maybe (Fn3 TextBlock_ String String Boolean)
_textValidation = toMaybe <<< getUnsafe [ "textValidation" ]

_verticalAlignment :: TextBlock_ -> Spot_
_verticalAlignment = getUnsafe [ "verticalAlignment" ]

_wrap :: TextBlock_ -> EnumValue_
_wrap = getUnsafe [ "wrap" ]
