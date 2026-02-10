module Data.String.Env
  ( Alias(..)
  , singleton
  , names
  , replaceLong
  , replaceShort
  , shortEnv
  , longEnv
  ) where

import Prelude
import Data.Array (foldl)

-- | The `Alias` type is used to represent strings that also have
-- | a shortened form. 
data Alias
  = Alias String String

derive instance eqAlias :: Eq Alias

instance showAlias :: Show Alias where
  show (Alias short long) = "Short: " <> show short <> ", Long: " <> show long

-- | Create an Alias who's short and long forms are the same.
singleton :: String -> Alias
singleton s = (Alias s s)

-- | A bank of common aliases. Singletons are used for compatibility.
-- | ``` yaml
-- | "dev", "development"
-- | "staging"
-- | "alpha"
-- | "beta"
-- | "prod", "production"
-- | "local", "locals"
-- | "remote"
-- | "test", "tests"
-- | "unit"
-- | "integration"
-- | "e2e", "endToEnd"
-- | ```
names =
  [ (Alias "dev" "development")
  , singleton "staging"
  , singleton "alpha"
  , singleton "beta"
  , (Alias "prod" "production")
  , (Alias "local" "locals")
  , singleton "remote"
  , (Alias "test" "tests")
  , singleton "unit"
  , singleton "integration"
  , (Alias "e2e" "endToEnd")
  ] ::
    Array Alias

-- | Replace a string with the long form of an alias.
replaceLong :: String -> Alias -> String
replaceLong s (Alias short long)
  | s == short = long
  | otherwise = s

-- | Replace a string with the short form of an alias.
replaceShort :: String -> Alias -> String
replaceShort s (Alias short long)
  | s == long = short
  | otherwise = s

-- | Replace a string with the long form of any matching alias
-- | from the list of common aliases.
longEnv :: String -> String
longEnv env = foldl replaceLong env names

-- | Replace a string with the short form of any matching alias
-- | from the list of common aliases.
shortEnv :: String -> String
shortEnv env = foldl replaceShort env names
