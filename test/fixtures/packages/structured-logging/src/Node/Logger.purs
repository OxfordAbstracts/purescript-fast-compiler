module Node.Logger where

import Prelude

import Effect.Class (class MonadEffect)
import Effect.Class.Console as Console
import Node.Logger.LogLevel (LogLevel(..))
import Node.Logger.LogLine (format, note)

info ∷ ∀ m. MonadEffect m ⇒ String → m Unit
info =
  Console.info
    <<< format
    <=< note INFO

warn ∷ ∀ m. MonadEffect m ⇒ String → m Unit
warn =
  Console.warn
    <<< format
    <=< note WARN

error ∷ ∀ m. MonadEffect m ⇒ String → m Unit
error =
  Console.error
    <<< format
    <=< note ERROR

log ∷ ∀ m. MonadEffect m ⇒ String → m Unit
log = info
