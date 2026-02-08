module Org.Test.Test02b where


import Prelude ((#), (<$>))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.empty
    # Org.todoSequence
        ( Org.Progress <$> [ "NEXT", "TODO", "WAITING", "SOMEDAY", "PROJ" ])
        ( Org.Finish   <$> [ "DONE", "CANCELLED" ])