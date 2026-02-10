-- | RequestAnimationFrame bindings
-- |
-- | Provides browser animation frame timing for tick-based animations.
module Hylograph.Transition.RAF
  ( AnimationFrameId
  , Timestamp
  , requestAnimationFrame
  , cancelAnimationFrame
  , performanceNow
  ) where

import Prelude

import Effect (Effect)

-- | Opaque ID for a scheduled animation frame
foreign import data AnimationFrameId :: Type

-- | High-resolution timestamp in milliseconds
type Timestamp = Number

-- | Schedule a callback for the next animation frame.
-- | The callback receives a high-resolution timestamp.
foreign import requestAnimationFrame_ :: (Timestamp -> Effect Unit) -> Effect AnimationFrameId

-- | Cancel a scheduled animation frame.
foreign import cancelAnimationFrame_ :: AnimationFrameId -> Effect Unit

-- | Get current high-resolution timestamp.
foreign import performanceNow_ :: Effect Timestamp

-- | Schedule a callback for the next animation frame.
requestAnimationFrame :: (Timestamp -> Effect Unit) -> Effect AnimationFrameId
requestAnimationFrame = requestAnimationFrame_

-- | Cancel a scheduled animation frame.
cancelAnimationFrame :: AnimationFrameId -> Effect Unit
cancelAnimationFrame = cancelAnimationFrame_

-- | Get current high-resolution timestamp.
performanceNow :: Effect Timestamp
performanceNow = performanceNow_
