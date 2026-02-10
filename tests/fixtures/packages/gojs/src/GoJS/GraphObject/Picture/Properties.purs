module GoJS.GraphObject.Picture.Properties where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn1, EffectFn2)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Rect_, Spot_)
import GoJS.GraphObject.Picture.PictureElement (PictureElement, whichPictureElement)
import GoJS.GraphObject.Types (Picture_)
import GoJS.Unsafe (getUnsafe)
import Web.Event.Event (Event)

_element :: Picture_ -> PictureElement
_element = whichPictureElement <<< getUnsafe [ "element" ]

_errorFunction :: Picture_ -> Maybe (EffectFn2 Picture_ Event Unit)
_errorFunction = toMaybe <<< getUnsafe [ "errorFunction" ]

_flip :: Picture_ -> EnumValue_
_flip = getUnsafe [ "flip" ]

_imageAlignment :: Picture_ -> Spot_
_imageAlignment = getUnsafe [ "imageAlignment" ]

_imageStretch :: Picture_ -> EnumValue_
_imageStretch = getUnsafe [ "imageStretch" ]

_source :: Picture_ -> String
_source = getUnsafe [ "source" ]

_sourceCrossOrigin :: Picture_ -> Maybe (EffectFn1 Picture_ String)
_sourceCrossOrigin = toMaybe <<< getUnsafe [ "sourceCrossOrigin" ]

_sourceRect :: Picture_ -> Rect_
_sourceRect = getUnsafe [ "sourceRect" ]

_successFunction :: Picture_ -> Maybe (EffectFn2 Picture_ Event Unit)
_successFunction = toMaybe <<< getUnsafe [ "successFunction" ]
