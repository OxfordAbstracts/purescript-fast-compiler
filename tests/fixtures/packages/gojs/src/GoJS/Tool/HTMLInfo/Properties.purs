module GoJS.Tool.HTMLInfo.Properties where

import Prelude

import Data.Function.Uncurried (Fn0)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect.Uncurried (EffectFn2, EffectFn3)
import GoJS.Diagram (class IsDiagram)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Tool.Types (HTMLInfo_)
import GoJS.Tool (class IsTool)
import GoJS.Unsafe (getUnsafe)
import Web.HTML (HTMLElement)

_hide :: forall d t. IsDiagram d => IsTool t => HTMLInfo_ -> EffectFn2 d t Unit
_hide = getUnsafe ["hide"]

_mainElement :: HTMLInfo_ -> Maybe HTMLElement
_mainElement = toMaybe <<< getUnsafe ["mainElement"]

_show :: forall g d t. IsGraphObject g => IsDiagram d => IsTool t => HTMLInfo_ -> EffectFn3 g d t Unit
_show = getUnsafe ["show"]

-- Typically returns a string
_valueFunction :: HTMLInfo_ -> Maybe (Fn0 String)
_valueFunction = toMaybe <<< getUnsafe ["valueFunction"]