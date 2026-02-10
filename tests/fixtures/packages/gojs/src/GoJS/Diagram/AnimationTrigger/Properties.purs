module GoJS.Diagram.AnimationTrigger.Properties where

import Data.Nullable (Nullable)
import GoJS.Diagram.Types (AnimationTrigger_, EasingFunction)
import GoJS.EnumValue (EnumValue_)
import GoJS.Unsafe (getUnsafe)

_animationSettings :: forall @a. AnimationTrigger_ -> {duration :: Nullable Boolean, easing :: Nullable EasingFunction, finished :: Nullable a} 
_animationSettings = getUnsafe [ "animationSettings" ]

_propertyName :: AnimationTrigger_ -> String
_propertyName = getUnsafe [ "propertyName" ]

_startCondition :: AnimationTrigger_ -> EnumValue_
_startCondition = getUnsafe [ "startCondition" ]
