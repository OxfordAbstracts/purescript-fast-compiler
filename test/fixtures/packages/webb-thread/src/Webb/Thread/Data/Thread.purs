module Webb.Thread.Data.Thread where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Effect.Aff (Fiber)


data Thread = Stopped | Starting | Running (Fiber Unit)

instance Eq Thread where
  eq (Stopped) (Stopped) = true
  eq (Starting) (Starting) = true
  eq (Running _) (Running _) = true
  eq _x _y = false

derive instance Generic Thread _
instance Show Thread where 
  show (Running _) = "Running"
  show (Starting) = "Starting"
  show (Stopped) = "Stopped"

-- Transitions the state to Stopped. Always can transition to stopped.
stop :: Thread -> Thread
stop _ = Stopped

starting :: Thread -> Thread
starting (Stopped) = Starting
starting x = x

-- We only transition to running if we're still starting.
running :: Fiber Unit -> Thread -> Thread
running fiber' (Starting) = Running fiber'
running _ x = x

fiber :: Thread -> Maybe (Fiber Unit)
fiber (Running fiber') = Just fiber'
fiber _ = Nothing

isStopped :: Thread -> Boolean
isStopped (Stopped) = true
isStopped _ = false

isStarting :: Thread -> Boolean
isStarting (Starting) = true
isStarting _ = false

isRunning :: Thread -> Boolean
isRunning (Running _) = true
isRunning _ = false