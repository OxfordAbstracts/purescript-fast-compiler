module Web.Intersection.Observer.Options
  ( IntersectionObserverOptions
  , RootMargin
  , root
  , rm
  , rootMargin
  , threshold
  , thresholds
  ) where
import Data.String (joinWith)
import Data.Options (Option, opt)
import CSS.Size (Size,sizeToString)
import Web.DOM.Element (Element)
import Prelude ((<$>))

data IntersectionObserverOptions

root :: Option IntersectionObserverOptions Element
root = opt "root"

newtype RootMargin = RootMargin String

rm :: forall a . Size a -> Size a -> Size a -> Size a -> RootMargin
rm t r b l = RootMargin (joinWith " " (sizeToString <$> [t,r,b,l])) 

rootMargin :: Option IntersectionObserverOptions RootMargin
rootMargin = opt "rootMargin"

threshold :: Option IntersectionObserverOptions Number
threshold = opt "threshold"

thresholds :: Option IntersectionObserverOptions (Array Number)
thresholds = opt "threshold"


