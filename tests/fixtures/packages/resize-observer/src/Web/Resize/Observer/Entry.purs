module Web.Resize.Observer.Entry where
import Web.DOM.Element (DOMRect,Element)

type ResizeObserverEntry =
  { contentRect :: DOMRect
  , target :: Element
  }
