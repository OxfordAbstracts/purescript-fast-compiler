
module ECharts where

import Prelude (Unit)
import Effect (Effect)
import Web.DOM.Internal.Types (Element)
import Data.Function.Uncurried (Fn1)

type ChartRef = {}
type EventName = String
type EventQuery = String
type Callback r = Fn1 r (Effect Unit)

-- Starts a Chart in a given DOM element.
foreign import init :: Element -> Effect ChartRef

-- Starts a Chart looking up a DOM element with `document.getElementById` .
foreign import initById :: String -> Effect ChartRef

-- Wraps ECharts's `showLoading` .
foreign import showLoading :: ChartRef -> Effect Unit

-- Wraps ECharts's `hideLoading` .
foreign import hideLoading :: ChartRef -> Effect Unit

-- Wraps ECharts's `setOptions` .
-- The particular record type must be defined at the call site.
foreign import setOptions :: forall r. ChartRef -> {|r} -> Effect Unit

-- Sets a callback on EChart using `chart.on` with no query.
-- The work to type effect.
-- The particular callback object type must be defined at the call site.
foreign import on :: forall r. ChartRef -> EventName -> Callback {|r} -> Effect Unit

-- Sets a callback on EChart using `chart.on` with a given query.
foreign import onQuery :: forall r. ChartRef -> EventName -> EventQuery -> Callback {|r} -> Effect Unit
