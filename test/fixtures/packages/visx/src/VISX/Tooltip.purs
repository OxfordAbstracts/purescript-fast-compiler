module VISX.Tooltip where

import Prelude
import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, runEffectFn1)
import Foreign (Foreign)
import React.Basic.Hooks (Hook, ReactComponent, unsafeHook)
import Untagged.Union (UndefinedOr, uorToMaybe)

foreign import data UseTooltip ∷ Type → Type → Type

type TooltipPayload a
  = { tooltipData ∷ a, tooltipLeft ∷ Number, tooltipTop ∷ Number }

type UseTooltipValuesImpl a
  = { hideTooltip ∷ Effect Unit
    , showTooltip ∷ EffectFn1 (TooltipPayload a) Unit
    , tooltipData ∷ UndefinedOr a
    , tooltipLeft ∷ UndefinedOr Number
    , tooltipOpen ∷ Boolean
    , tooltipTop ∷ UndefinedOr Number
    , updateTooltip ∷ EffectFn1 (TooltipPayload a) Unit
    }

type UseTooltipValues a
  = { hideTooltip ∷ Effect Unit
    , showTooltip ∷ TooltipPayload a → Effect Unit
   , tooltipData ∷ Maybe a
    , tooltipLeft ∷ Maybe Number
    , tooltipOpen ∷ Boolean
    , tooltipTop ∷ Maybe Number
    , updateTooltip ∷ TooltipPayload a → Effect Unit
    }

foreign import useTooltipImpl ∷ ∀ a. Effect (UseTooltipValuesImpl a)

useTooltip ∷ ∀ a. Hook (UseTooltip a) (UseTooltipValues a)
useTooltip =
  unsafeHook useTooltipImpl
    <#> \baseProps →
        { hideTooltip: baseProps.hideTooltip
        , showTooltip: baseProps.showTooltip # runEffectFn1
        , tooltipData: uorToMaybe baseProps.tooltipData
        , tooltipLeft: uorToMaybe baseProps.tooltipLeft
        , tooltipOpen: baseProps.tooltipOpen
        , tooltipTop: uorToMaybe baseProps.tooltipTop
        , updateTooltip: baseProps.updateTooltip # runEffectFn1
        }

foreign import tooltipImpl ∷ ∀ p. ReactComponent p
foreign import defaultStylesImpl ∷ Foreign
foreign import tooltipWithBoundsImpl ∷ ∀ p. ReactComponent p
foreign import portalImpl ∷ ∀ p. ReactComponent p
