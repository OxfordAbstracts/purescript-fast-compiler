module GoJS.Diagram.Overview.Constructors where

import Effect (Effect)
import GoJS.Diagram.Types (Overview_)
import GoJS.Unsafe.Constructor (constructor1)

newOverview :: String -> Effect Overview_
newOverview = constructor1 "Overview"
