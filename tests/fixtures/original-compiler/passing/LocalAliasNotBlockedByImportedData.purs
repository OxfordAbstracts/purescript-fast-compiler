module Main where

import Component as Component
import Shared (ModelExt)
import Effect.Console (log)

-- This module defines a local `type Model` alias AND imports `Component`
-- which has `data Model`. The local alias must expand correctly:
-- con_zero_blockers must not block locally-defined aliases.

type Model = ModelExt (page :: String, component :: Component.Model)

-- LazyUpdate references Model in its body — this exercises alias expansion
-- of the local zero-param alias through another local alias.
type LazyUpdate = Model -> String

update :: LazyUpdate
update m = m.name

getName :: Model -> String
getName m = m.name

getCount :: Model -> Int
getCount m = m.count

getPage :: Model -> String
getPage m = m.page

main = log "Done"
