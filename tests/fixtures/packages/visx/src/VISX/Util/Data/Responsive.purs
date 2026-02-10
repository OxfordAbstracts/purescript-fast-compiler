module VISX.Util.Data.Responsive
  ( ParentSizeProps
  , ParentSizeState
  , RenderParentSizeChildren
  , ScaleSVGProps
  , parentSize
  , scaleSVG
  , withParentSize
  , withParentSizeModern
  , withScreenSize
  ) where

import Prelude
import Data.Nullable (Nullable)
import Data.Time.Duration (Milliseconds)
import Effect.Uncurried (EffectFn1)
import Prim.Row (class Union)
import React.Basic (JSX, ReactComponent, Ref)
import React.Basic.DOM (CSS)
import Web.DOM (Node)

foreign import withScreenSize ∷ ∀ r. ReactComponent { screenWidth ∷ Number, screenHeight ∷ Number | r } → ReactComponent { | r }
foreign import withParentSize ∷ ∀ r. ReactComponent { parentWidth ∷ Number, parentHeight ∷ Number | r } → ReactComponent { | r }
foreign import withParentSizeModern ∷ ∀ r. ReactComponent { parentWidth ∷ Number, parentHeight ∷ Number | r } → ReactComponent { | r }

-- Scale SVG
scaleSVG ∷ ∀ p p_. Union p p_ ScaleSVGProps ⇒ ReactComponent { | p }
scaleSVG = scaleSVGImpl
foreign import scaleSVGImpl ∷ ∀ r. ReactComponent { | r }

type ScaleSVGProps
  = ( children ∷ Array JSX
    , height ∷ Number
    , width ∷ Number
    , innerRef ∷ ∀ ref. Ref ref
    , preserveAspectRatio ∷ String
    , xOrigin ∷ String
    , yOrigin ∷ String
    )

-- Parent Size
parentSize ∷
  ∀ p p_.
  Union p p_ ParentSizeProps ⇒
  ReactComponent { children ∷ RenderParentSizeChildren | p }
parentSize = parentSizeImpl
foreign import parentSizeImpl ∷ ∀ r. ReactComponent { | r }

type ParentSizeState
  = ( width ∷ Number, height ∷ Number, top ∷ Number, left ∷ Number )

type RenderParentSizeChildren
  = { ref ∷ Nullable (Ref Node)
    , resize ∷ EffectFn1 { | ParentSizeState } Unit
    | ParentSizeState
    } →
    JSX

type ParentSizeProps
  = ( children ∷ RenderParentSizeChildren
    , className ∷ String
    , debounceTime ∷ Milliseconds
    , enableDebounceLeadingCall ∷ Boolean
    , ignoreDimensions ∷ Array String
    , parentSizeStyles ∷ CSS
    )
