module CommandLine where

import Prelude

import Data.Array as Array
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Uncurried (EffectFn2, runEffectFn2)
import Node.Buffer (Buffer)
import Node.Process as Process

{- Tools to run typical commands from within a Purescript program running on Node.

-}

foreign import anyCommand :: EffectFn2 String ShellOptions Buffer

newtype CommandLine = C Unit

newCommandLine :: forall m. MonadEffect m => m CommandLine
newCommandLine = pure $ C unit

-- The command-line arguments to the nodeJS script. Does NOT include
-- the name of the script or the name of the Node executable.
args :: forall m. MonadEffect m => CommandLine -> m (Array String)
args _ = liftEffect do 
  argv <- Process.argv
  pure $ Array.drop 2 argv

type ShellOptions = 
  { forwardOutput :: Boolean
  }

-- Run any shell command, discarding the output.
shell :: forall m. MonadEffect m => 
  CommandLine -> String -> m Buffer
shell self string = do
  shell' self { forwardOutput: true } string

shell' :: forall m. MonadEffect m => 
  CommandLine -> ShellOptions -> String -> m Buffer
shell' _self options command = do 
  buffer <- liftEffect do runEffectFn2 anyCommand command options
  pure $ buffer
  
spagoBuild :: forall m. MonadEffect m =>
  CommandLine -> m Unit
spagoBuild self = void $ shell self "spago build"

spagoTest :: forall m. MonadEffect m =>
  CommandLine -> m Unit
spagoTest self = void $ shell self "spago test"
