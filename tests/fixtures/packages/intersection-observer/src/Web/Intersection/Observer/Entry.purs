module Web.Intersection.Observer.Entry where
import Web.DOM.Element (DOMRect,Element)

type IntersectionObserverEntry =
  { boundingClientRect :: DOMRect
  , intersectionRatio :: Number
  , intersectionRect :: DOMRect
  , isIntersecting :: Boolean
  , rootBounds :: DOMRect
  , target :: Element
  , time :: Number
  }
