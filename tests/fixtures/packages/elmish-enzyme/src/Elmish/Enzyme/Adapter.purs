module Elmish.Enzyme.Adapter
  ( Adapter
  , unofficialReact_17
  , react_16_4
  , react_16_3
  , react_16_2
  , react_16_1
  , react_15_5
  , react_15_4
  , react_14
  , react_13
  )
  where

import Prelude (($))
import Effect (Effect)
import Effect.Aff (Aff)
import Control.Promise (toAffE, Promise)

foreign import data Adapter :: Type

unofficialReact_17 = adapter "@wojtekmaj/enzyme-adapter-react-17" :: Aff Adapter -- ^17.0.0
react_16_4 = adapter "enzyme-adapter-react-16" :: Aff Adapter                    -- ^16.4.0-0
react_16_3 = adapter "enzyme-adapter-react-16.3" :: Aff Adapter                  -- ~16.3.0-0
react_16_2 = adapter "enzyme-adapter-react-16.2" :: Aff Adapter                  -- ~16.2
react_16_1 = adapter "enzyme-adapter-react-16.1" :: Aff Adapter                  -- ~16.0.0-0 || ~16.1
react_15_5 = adapter "enzyme-adapter-react-15" :: Aff Adapter                    -- ^15.5.0
react_15_4 = adapter "enzyme-adapter-react-15.4" :: Aff Adapter                  --  15.0.0-0 - 15.4.x
react_14 = adapter "enzyme-adapter-react-14" :: Aff Adapter                      -- ^0.14.0
react_13 = adapter "enzyme-adapter-react-13" :: Aff Adapter                      -- ^0.13.0

foreign import adapterImpl :: String -> Effect (Promise Adapter)

adapter :: String -> Aff Adapter
adapter pkg = toAffE $ adapterImpl pkg
