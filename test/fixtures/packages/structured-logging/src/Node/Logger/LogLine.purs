module Node.Logger.LogLine where

import Prelude

import Data.Argonaut.Core (jsonEmptyObject, stringify)
import Data.Argonaut.Encode ((:=), (~>))
import Data.JSDate (now, toISOString)
import Effect.Class (class MonadEffect, liftEffect)
import Node.Logger.LogLevel (LogLevel)

type LogLine =
  { timestamp ∷ String
  , level ∷ LogLevel
  , message ∷ String
  }

format ∷ LogLine → String
format { timestamp, level, message } = stringify
  $ "message" := message
      ~> "level" := show level
      ~> "timestamp" := timestamp
      ~> jsonEmptyObject

note ∷ ∀ m. MonadEffect m ⇒ LogLevel → String → m LogLine
note level message = do
  timestamp ← liftEffect $ toISOString =<< now
  pure $ { timestamp, level, message }
