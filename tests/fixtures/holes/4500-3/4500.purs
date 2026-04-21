module Main where

import Prelude

import Data.Reflectable (class Reflectable, reflectType)
import Type.Proxy (Proxy(..))
import Effect.Console (log)

reflect :: forall @t v . Reflectable t v => ?test
reflect = reflectType (Proxy @t)

use :: String
use = show { asdf: reflect @"asdf" }

main = log "Done"
