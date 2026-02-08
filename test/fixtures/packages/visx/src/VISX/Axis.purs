module VISX.Axis
  ( LabelProps
  , DefaultAxisProps
  , AxisProps
  , AxisRendererProps
  , TickRendererProps
  , axis
  , axisBottom
  , labelProps
  , axisLeft
  , axisRight
  , axisTop
  ) where

import D3.Format (D3Format)
import Data.Function.Uncurried (Fn2)
import Effect.Uncurried (EffectFn1)
import Prim.Row (class Union)
import React.Basic (JSX, ReactComponent)
import React.Basic.DOM.SVG (Props_text)
import Unsafe.Coerce (unsafeCoerce)
import VISX.Scale (class Scale)

type AxisRendererProps = {}

type TickRendererProps = {}

foreign import data LabelProps ∷ Type

labelProps ∷ ∀ attrs attrs_. Union attrs attrs_ Props_text ⇒ { | attrs } → LabelProps
labelProps = unsafeCoerce

type AxisProps ∷ ∀ k. Row Type → Type → k → Row Type
type AxisProps r domain codomain =
  ( scale ∷ ∀ scale. scale domain codomain
  , axisClassName ∷ String
  , axisLineClassName ∷ String
  , children ∷ AxisRendererProps → JSX
  , hideAxisLine ∷ Boolean
  , hideTicks ∷ Boolean
  , hideZero ∷ Boolean
  , label ∷ String
  , labelClassName ∷ String
  , labelOffset ∷ Number
  , labelProps ∷ LabelProps
  , left ∷ Number
  , numTicks ∷ Int
  , orientation ∷ String
  , rangePadding ∷ Number
  , stroke ∷ String
  , strokeDasharray ∷ String
  , strokeWidth ∷ String
  , tickClassName ∷ String
  , tickComponent ∷ TickRendererProps → JSX
  , tickFormat ∷ domain → String
  , tickLabelProps ∷ Fn2 domain Int LabelProps
  , tickLength ∷ Number
  , ticksComponent ∷ TickRendererProps → JSX
  , tickStroke ∷ String
  , tickTransform ∷ String
  -- , tickValues :: NoIdea
  , top ∷ Number
  | r
  )

type DefaultAxisProps ∷ ∀ k. Type → k → Row Type
type DefaultAxisProps domain codomain = AxisProps (width ∷ String, height ∷ String, display ∷ String) domain codomain

axis ∷ ∀ scale domain codomain attrs attrs_. Scale (scale domain codomain) ⇒ Union attrs attrs_ (DefaultAxisProps domain codomain) ⇒ ReactComponent { scale ∷ scale domain codomain | attrs }
axis = axisImpl

axisLeft ∷ ∀ scale domain codomain attrs attrs_. Scale (scale domain codomain) ⇒ Union attrs attrs_ (DefaultAxisProps domain codomain) ⇒ ReactComponent { scale ∷ scale domain codomain | attrs }
axisLeft = axisLeftImpl

axisTop ∷ ∀ scale domain codomain attrs attrs_. Scale (scale domain codomain) ⇒ Union attrs attrs_ (DefaultAxisProps domain codomain) ⇒ ReactComponent { scale ∷ scale domain codomain | attrs }
axisTop = axisTopImpl

axisRight ∷ ∀ scale domain codomain attrs attrs_. Scale (scale domain codomain) ⇒ Union attrs attrs_ (DefaultAxisProps domain codomain) ⇒ ReactComponent { scale ∷ scale domain codomain | attrs }
axisRight = axisRightImpl

axisBottom ∷ ∀ scale domain codomain attrs attrs_. Scale (scale domain codomain) ⇒ Union attrs attrs_ (DefaultAxisProps domain codomain) ⇒ ReactComponent { scale ∷ scale domain codomain | attrs }
axisBottom = axisBottomImpl

foreign import axisImpl ∷ ∀ a. ReactComponent { | a }

foreign import axisTopImpl ∷ ∀ a. ReactComponent { | a }

foreign import axisBottomImpl ∷ ∀ a. ReactComponent { | a }

foreign import axisLeftImpl ∷ ∀ a. ReactComponent { | a }

foreign import axisRightImpl ∷ ∀ a. ReactComponent { | a }
