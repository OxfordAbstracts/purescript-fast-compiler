module XTerm.Decoration
  ( Decoration
  , marker
  , onRender
  , getElement
  , overviewRuler
  ) where

import Control.Alt (map)
import Control.Category ((<<<))
import Data.Maybe (Maybe)
import Data.Unit (Unit)
import Effect (Effect)
import Foreign (Foreign)
import Unsafe.Coerce (unsafeCoerce)
import Web.DOM (Element)
import XTerm.Decoration.OverviewRuler (OverviewRuler)
import XTerm.Disposable (Disposable)
import XTerm.DisposableWithEvent (class IsDisposableWithEvent)
import XTerm.Marker (Marker)
import XTerm.Utils (maybeUndefined)

data Decoration

instance IsDisposableWithEvent Decoration where
  toDisposableWithEvent = unsafeCoerce

foreign import marker :: Decoration -> Marker

foreign import onRender :: Decoration -> (Element -> Effect Unit) -> Effect Disposable

foreign import _getElement :: Decoration -> Effect Foreign

getElement :: Decoration -> Effect (Maybe Element)
getElement = map maybeUndefined <<< _getElement

foreign import _overviewRuler :: Decoration -> Foreign

overviewRuler :: Decoration -> Maybe OverviewRuler
overviewRuler = maybeUndefined <<< _overviewRuler
