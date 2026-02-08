module Org.Test.Test04d where


import Prelude (($), (<$>))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
    $ Org.db 
        [ Org.table
            [ Org.qrow' [ "I", "am", "a", "table" ]
            , Org.qrow' [ "with", "two", "rows", "!" ]
            ]
        , Org.blank
        , Org.table
            [ Org.qrow' [ "Tool", "Literate programming?", "Reproducible Research?", "Languages" ]
            , Org.tbreak
            , Org.qrow' [ "Javadoc", "partial", "no", "Java" ]
            , Org.qrow' [ "Haskell .lhs", "partial", "no", "Haskell" ]
            , Org.qrow' [ "noweb", "yes", "no", "any" ]
            , Org.qrow' [ "Sweave", "partial", "yes", "R" ]
            , Org.qrow' [ "Org-mode", "yes", "yes", "any" ]
            ]        
        ]