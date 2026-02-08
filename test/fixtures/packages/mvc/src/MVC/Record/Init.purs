module MVC.Record.Init
  ( class InitRecord
  , initRecord
  ) where

import MVC.Record (RecordState(..))

class
  InitRecord
    (inits :: Row Type)
    (rsta :: Row Type)
  where
  initRecord :: Record inits -> RecordState rsta

instance InitRecord inits inits where
  initRecord :: Record inits -> RecordState inits
  initRecord = RecordState