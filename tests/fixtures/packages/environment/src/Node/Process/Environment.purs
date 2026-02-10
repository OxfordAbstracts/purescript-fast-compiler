module Node.Process.Environment
  ( Environment(..)
  , detect
  , lookup
  , require
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String.Read (class Read, read)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (throw)
import Node.Process (lookupEnv)

data Environment = Development | Production

derive instance eqEnvironment ∷ Eq Environment

instance showEnvironment ∷ Show Environment where
  show Production = "production"
  show Development = "development"

instance readEnvironment ∷ Read Environment where
  read "production" = Just Production
  read "development" = Just Development
  read _ = Nothing

reject ∷ ∀ a. String → String → Maybe a → Effect a
reject message x = maybe (throw $ message <> ": " <> x) pure

lookup ∷ ∀ m. MonadEffect m ⇒ String → String → m String
lookup name fallback = liftEffect do
  env ← lookupEnv name
  pure $ fromMaybe fallback env

require ∷ ∀ m. MonadEffect m ⇒ String → m String
require name = liftEffect do
  env ← lookupEnv name
  reject "Missing environment variable" name env

detect ∷ ∀ m. MonadEffect m ⇒ m Environment
detect = liftEffect do
  env ← require "NODE_ENV"
  reject "Not a valid environment" env $ read env
