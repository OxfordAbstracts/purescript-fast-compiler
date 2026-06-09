module Test.Multi.ParallelModel where

import Test.Multi.ParallelInitA as InitA
import Test.Multi.ParallelInitB as InitB

-- Mirrors AdminDashboard.Model.Page: a sum type whose constructors
-- each wrap a DIFFERENT module's `PageModel` alias, all named
-- identically.
data Page
  = SoaaControlsPage InitA.PageModel
  | EventPage InitB.PageModel
