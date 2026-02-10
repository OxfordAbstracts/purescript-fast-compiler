module GoJS.Diagram.AnimationTrigger.Constructors where

import Effect (Effect)
import GoJS.Diagram.Types (AnimationTrigger_)
import GoJS.EnumValue (EnumValue_)
import GoJS.Unsafe (constructor1, constructor2, constructor3)

newAnimationTrigger :: String -> Effect AnimationTrigger_
newAnimationTrigger = constructor1 "AnimationTrigger"

newAnimationTrigger' :: forall animationSettings. String -> Record animationSettings -> Effect AnimationTrigger_
newAnimationTrigger' = constructor2 "AnimationTrigger"

newAnimationTrigger'' :: forall animationSettings. String -> Record animationSettings -> EnumValue_ -> Effect AnimationTrigger_
newAnimationTrigger'' = constructor3 "AnimationTrigger"