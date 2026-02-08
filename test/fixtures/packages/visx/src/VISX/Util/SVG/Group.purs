module VISX.Util.SVG.Group (group) where

import Prim.Row (class Union)
import React.Basic (JSX, ReactComponent, Ref)

foreign import groupImpl ∷ ∀ a. ReactComponent { | a }

type GroupProps =
  ( className ∷ String
  , innerRef ∷ ∀ r. Ref r
  , left ∷ Number
  , top ∷ Number
  , transform ∷ String
  , children ∷ Array JSX
  )

group ∷ ∀ attrs attrs_. Union attrs attrs_ GroupProps => ReactComponent { | attrs }
group = groupImpl
