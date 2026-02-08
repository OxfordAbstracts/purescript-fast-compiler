module GoJS.Diagram.AnimationManager.Properties where

import GoJS.Collection (Set_)
import GoJS.Diagram.Types (Animation_, AnimationManager_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_activeAnimations :: AnimationManager_ -> Set_ Animation_
_activeAnimations = getUnsafe [ "activeAnimations" ]

-- Read-only
_defaultAnimation :: AnimationManager_ -> Animation_
_defaultAnimation = getUnsafe [ "defaultAnimation" ]

_duration :: AnimationManager_ -> Number
_duration = getUnsafe [ "duration" ]

_initialAnimationStyle :: AnimationManager_ -> EnumValue_
_initialAnimationStyle = getUnsafe [ "initialAnimationStyle" ]

-- Read-only
_isAnimating :: AnimationManager_ -> Boolean
_isAnimating = getUnsafe [ "isAnimating" ]

_isEnabled :: AnimationManager_ -> Boolean
_isEnabled = getUnsafe [ "isEnabled" ]

_isInitial :: AnimationManager_ -> Boolean
_isInitial = getUnsafe [ "isInitial" ]

-- Read-only
_isTicking :: AnimationManager_ -> Boolean
_isTicking = getUnsafe [ "isTicking" ]
