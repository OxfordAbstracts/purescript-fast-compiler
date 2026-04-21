module ConZeroBlockerExport.Middle where

import ConZeroBlockerExport.AliasModule (T)
import ConZeroBlockerExport.DataModule (T(..)) as D

-- This module imports BOTH the alias and the data type.
-- The alias (record) is in type_aliases; the data type is in type_con_arities.
-- con_zero_blockers should prevent the alias from expanding T
-- in the exported value scheme for `event`, preserving the data type ref.

type EventRec = { name :: String, pt :: D.T }

event :: EventRec -> D.T
event r = r.pt
