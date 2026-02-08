-- | Docker Compose management for integration tests
-- |
-- | This module provides utilities for managing Docker Compose services
-- | in integration test suites. It uses FFI to call `docker compose` commands
-- | and provides functions compatible with PureScript's `bracket` pattern
-- | for guaranteed cleanup.
-- |
-- | ## Example Usage
-- |
-- | ```purescript
-- | import Yoga.Test.Docker as Docker
-- | import Effect.Aff (bracket)
-- |
-- | main = launchAff_ do
-- |   bracket
-- |     (Docker.startService "docker-compose.test.yml" 30)
-- |     (\_ -> Docker.stopService "docker-compose.test.yml")
-- |     (\_ -> runSpec spec)
-- | ```
module Yoga.Test.Docker
  ( startService
  , stopService
  , waitForHealthy
  , dockerComposeUp
  , dockerComposeDown
  , isServiceHealthy
  ) where

import Prelude

import Effect.Aff (Aff, delay, throwError)
import Effect.Class (liftEffect)
import Effect.Exception (error)
import Data.Time.Duration (Milliseconds(..))

-- | Start a Docker Compose service from the given compose file
foreign import dockerComposeUp :: String -> Aff Unit

-- | Stop a Docker Compose service from the given compose file
foreign import dockerComposeDown :: String -> Aff Unit

-- | Check if a service defined in the compose file is healthy
foreign import isServiceHealthy :: String -> Aff Boolean

-- | Wait for a service to become healthy, retrying up to maxAttempts times
-- | Each attempt waits 1 second before checking again.
waitForHealthy :: String -> Int -> Aff Unit
waitForHealthy composeFile maxAttempts = go 0
  where
  go n
    | n >= maxAttempts = throwError $ error "Service failed to become healthy"
    | otherwise = do
        healthy <- isServiceHealthy composeFile
        if healthy then
          liftEffect $ pure unit
        else do
          delay (Milliseconds 1000.0)
          go (n + 1)

-- | Start a Docker Compose service and wait for it to be healthy
-- |
-- | This is a convenience function that combines `dockerComposeUp` and `waitForHealthy`.
-- | Use with `bracket` for guaranteed cleanup:
-- |
-- | ```purescript
-- | bracket
-- |   (Docker.startService "docker-compose.test.yml" 30)
-- |   (\_ -> Docker.stopService "docker-compose.test.yml")
-- |   (\_ -> runTests)
-- | ```
startService :: String -> Int -> Aff Unit
startService composeFile maxWaitSeconds = do
  dockerComposeUp composeFile
  waitForHealthy composeFile maxWaitSeconds

-- | Stop a Docker Compose service
-- |
-- | This should be called in the cleanup phase of `bracket` to ensure
-- | the service is stopped even if tests fail.
stopService :: String -> Aff Unit
stopService = dockerComposeDown
