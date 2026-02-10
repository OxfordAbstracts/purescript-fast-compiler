module VISX.Util.SVG.Event where

import Prelude
import Data.Maybe (Maybe)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Effect (Effect)
import Effect.Uncurried (EffectFn1, runEffectFn1)
import React.Basic.Events (SyntheticEvent)

foreign import localPointImpl ∷ EffectFn1 SyntheticEvent (Nullable { x ∷ Number, y ∷ Number })

localPoint ∷
  SyntheticEvent ->
  Effect (Maybe { x ∷ Number, y ∷ Number })
localPoint = runEffectFn1 localPointImpl <#> map Nullable.toMaybe
