-- Regression test: module re-exports should not include names from
-- qualified-only imports (import M as Q with no explicit import list).
--
-- Here, Lib exports both `foo` and `bar`. We import `bar` explicitly and
-- also do a qualified-only import `as L`. The `module Lib` re-export should
-- only include `bar` (from the explicit import), not `foo` (from the
-- qualified-only import). Wrapper also exports `foo`, so if the qualified
-- import leaked `foo` from Lib, it would cause a false ExportConflict.
module QualifiedImportReexport
  ( module QualifiedImportReexport.Lib
  , module QualifiedImportReexport.Wrapper
  ) where

import QualifiedImportReexport.Lib (bar)
import QualifiedImportReexport.Lib as L
import QualifiedImportReexport.Wrapper (foo)
