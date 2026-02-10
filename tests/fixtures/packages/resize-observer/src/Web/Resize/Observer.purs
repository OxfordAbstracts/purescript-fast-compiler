module Web.Resize.Observer
  ( ResizeObserver
  , ResizeObserverCallback
  , newResizeObserver
  , observe
  , observeBorderBox
  , unobserve
  ) where
import Web.Resize.Observer.Entry
import Web.DOM.Element (Element)
import Effect (Effect)
import Prelude (Unit)

foreign import data ResizeObserver :: Type

type ResizeObserverCallback =
   Array ResizeObserverEntry -> ResizeObserver -> Effect Unit

newResizeObserver :: ResizeObserverCallback
                  -> Effect ResizeObserver
newResizeObserver c = _newResizeObserver c

foreign import _newResizeObserver :: ResizeObserverCallback
                                  -> Effect ResizeObserver

foreign import observe :: ResizeObserver -> Element -> Effect Unit 

foreign import observeBorderBox :: ResizeObserver -> Element -> Effect Unit 

foreign import unobserve :: ResizeObserver -> Element -> Effect Unit 
