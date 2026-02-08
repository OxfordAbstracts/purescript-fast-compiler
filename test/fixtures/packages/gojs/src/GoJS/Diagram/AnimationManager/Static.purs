module GoJS.Diagram.AnimationManager.Static where

import Prelude

import Effect (Effect)
import Effect.Uncurried (EffectFn7)
import GoJS.Diagram.Types (Animation_, EasingFunction)
import GoJS.Unsafe (callStatic2)

defineAnimationEffect_
  :: String
  -> ( forall obj startVal endVal
        . EffectFn7 obj startVal endVal EasingFunction Number Number Animation_ Unit
     )
  -> Effect Unit
defineAnimationEffect_ = callStatic2 "AnimationManager" "defineAnimationEffect"
