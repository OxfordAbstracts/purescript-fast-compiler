module Org.Test.Test03b where


import Prelude (($))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.ds
            [ Org.sec 1 [ Org.text "First Level Heading" ] $
                Org.dbs
                    [ Org.para
                        [ Org.text "Some text here", Org.br
                        , Org.text "And another line", Org.br
                        ]
                    , Org.para
                        [ Org.text "And another paragraph"
                        ]
                    ]
                    [ Org.sec 2 [ Org.text "Second Level Heading" ] $
                        Org.dbs
                            [ Org.para [ Org.text "Here some text as well" ] ]
                            [ Org.sec 3 [ Org.text "Third Level Heading" ] $
                                Org.dbs
                                    [ Org.para [ Org.text "The paragraph inside the third level" ] ]
                                    [ Org.sec 4 [ Org.text "Fourth Level Heading" ] $
                                        Org.db
                                            [ Org.para [ Org.text "Let's see if we have text here" ] ]
                                    ]
                            ]
                    ]
            ]