module Org.Test.Test03a where


import Prelude (($))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.ds
            [ Org.sec 1 [ Org.text "First Level Heading" ] $
                Org.ssec 2 [ Org.text "Second Level Heading" ] $
                    Org.ssec 3 [ Org.text "Third Level Heading" ] $
                        Org.ssec 4 [ Org.text "Fourth Level Heading" ] $
                            Org.emptyDoc
                            -- Org.db [ Org.para [ Org.br ] ]
            ]