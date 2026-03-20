module Main where

import DataModule (ProgramType(..), showPT)
import AliasModule as A
import Effect.Console (log)

-- Uses the data type ProgramType (not the alias).
-- When exporting, zonk_con_blockers must prevent the alias from
-- being expanded incorrectly in the exported type scheme.
usePT :: ProgramType -> String
usePT pt = showPT pt

mkTalk :: ProgramType
mkTalk = Talk

-- Also use the alias through its qualified name
mkAlias :: A.ProgramType
mkAlias = { name: "test", code: 1 }

main = log "Done"
