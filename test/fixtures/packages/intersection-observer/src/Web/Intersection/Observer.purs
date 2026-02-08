module Web.Intersection.Observer
  ( IntersectionObserver
  , IntersectionObserverCallback
  , newIntersectionObserver
  , observe
  , unobserve
  ) where
import Web.Intersection.Observer.Entry
import Web.Intersection.Observer.Options (IntersectionObserverOptions)
import Web.DOM.Element (Element)
import Data.Options (Options,options)
import Foreign (Foreign)
import Effect (Effect)
import Prelude (Unit)

foreign import data IntersectionObserver :: Type

type IntersectionObserverCallback =
   Array IntersectionObserverEntry -> IntersectionObserver -> Effect Unit

newIntersectionObserver :: IntersectionObserverCallback
                        -> Options IntersectionObserverOptions
                        -> Effect IntersectionObserver
newIntersectionObserver c o = _newIntersectionObserver c (options o)

foreign import _newIntersectionObserver :: IntersectionObserverCallback
                                        -> Foreign
                                        -> Effect IntersectionObserver

foreign import observe :: IntersectionObserver -> Element -> Effect Unit 

foreign import unobserve :: IntersectionObserver -> Element -> Effect Unit 
