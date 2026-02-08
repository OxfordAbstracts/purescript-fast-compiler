module Org.Test.Test02a where


import Prelude ((#))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.empty
        # Org.meta_kw (Org.kw "title" "The glories of Org")
        # Org.meta_kw (Org.kw "author" "A. Org Author")