module GoJS.Diagram.Animation.Properties where

import Prelude

import Effect.Uncurried (EffectFn1)
import GoJS.Diagram.Types (Animation_, EasingFunction)
import GoJS.Unsafe (getUnsafe)

_duration :: Animation_ -> Number
_duration = getUnsafe [ "duration" ]

_easing :: Animation_ -> EasingFunction
_easing = getUnsafe [ "easing" ]

_finished :: Animation_ -> (EffectFn1 Animation_ Unit)
_finished = getUnsafe [ "finished" ]

-- Read-only
_isAnimating :: Animation_ -> Boolean
_isAnimating = getUnsafe [ "isAnimating" ]

_isViewportUnconstrained :: Animation_ -> Boolean
_isViewportUnconstrained = getUnsafe [ "isViewportUnconstrained" ]

_reversible :: Animation_ -> Boolean
_reversible = getUnsafe [ "reversible" ]

_runCount :: Animation_ -> Number
_runCount = getUnsafe [ "runCount" ]