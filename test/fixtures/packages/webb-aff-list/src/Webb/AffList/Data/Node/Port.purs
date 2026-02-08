module Webb.AffList.Data.Node.Port where

import Prelude

import Effect.Aff (Error)

-- A port can deliver notice of closure, of value, or of error.
data PortValue a = Closed | Value a | Err Error