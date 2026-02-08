module Which
  ( WhichOptions(..)
  , whichSync
  , whichAllSync
  -- Options
  , path
  , pathExt
  ) where

import Prelude
import Data.Array.NonEmpty (NonEmptyArray, fromArray)
import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe, toNullable)
import Data.Options (Option, Options, opt, optional, options)
import Effect (Effect)
import Effect.Uncurried (EffectFn2, runEffectFn2)
import Foreign (Foreign)

foreign import data WhichOptions :: Type

-- | The path to use in place of the `PATH` environment variable.
path :: Option WhichOptions (Maybe String)
path = optional $ opt "path"

-- | The path to use in place of the `PATHEXT` environment variable.
pathExt :: Option WhichOptions (Maybe String)
pathExt = optional $ opt "pathExt"

fromOptions :: Maybe (Options WhichOptions) -> Nullable Foreign
fromOptions = toNullable <<< map options

foreign import whichSyncImpl :: EffectFn2 String (Nullable Foreign) (Nullable String)

-- | Returns the first instance of a specified executable in the `PATH`
-- | environment variable.
-- |
-- | Returns `Nothing` if the executable is not found.
whichSync :: Maybe (Options WhichOptions) -> String -> Effect (Maybe String)
whichSync opts command = do
  result <- runEffectFn2 whichSyncImpl command $ fromOptions opts
  pure $ toMaybe result

foreign import whichAllSyncImpl :: EffectFn2 String (Nullable Foreign) (Nullable (Array String))

-- | Returns all instances of a specified executable in the `PATH` environment
-- | variable.
-- |
-- | Returns `Nothing` if no executables are found.
whichAllSync :: Maybe (Options WhichOptions) -> String -> Effect (Maybe (NonEmptyArray String))
whichAllSync opts command = do
  result <- runEffectFn2 whichAllSyncImpl command $ fromOptions opts
  pure
    $ toMaybe result
    >>= fromArray
