module Org.Test.Test03d where


import Prelude (($), (#))

import Data.Text.Format.Org.Types (OrgFile, Todo(..), Priority(..))
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.ds
            [ Org.tag "single" 
            $ Org.sec1 1 (Org.text "A Heading") $
                Org.ds
                    [ Org.tag "several" $ Org.tag "tags" $ Org.sece1 2 (Org.text "Sub-Topic 1")
                    , Org.sece1 2 (Org.text "Sub-Topic 2")
                    , Org.sece1 3 (Org.text "Additional entry") # Org.tag "some-tag"
                    ]
            ]