module Org.Test.Test03e where


import Prelude (($), (#))

import Data.Text.Format.Org.Types (OrgFile, Todo(..), Priority(..))
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.dbs
            [ Org.para1 $ Org.text "An introduction." ]
            [ Org.sec1 1 (Org.text "A Heading") $
                Org.dbs
                    [ Org.para1 $ Org.text "Some text." ]
                    [ Org.sece1 2 (Org.text "Sub-Topic 1")
                    , Org.sece1 2 (Org.text "Sub-Topic 2")
                    , Org.sece1 3 (Org.text "Additional entry")
                    ]
            , Org.sec1 1 (Org.text "") $
                Org.ds
                    [ Org.set Done $ Org.sec1 2 (Org.text "") $
                        Org.ssec 3 [ Org.text "Some e-mail" ] $
                            Org.ds
                                [ Org.sece1 4 (Org.text "Title")
                                    # Org.set Todo
                                    # Org.priority (Alpha 'A')
                                    # Org.tag "a2%"
                                    # Org.tag "tag"
                                    # Org.comment
                                ]
                    ]
            ]