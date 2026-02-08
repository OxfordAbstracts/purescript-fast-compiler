module Org.Test.Test04i where


import Prelude (($), (#))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Types (ListType(..))
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.ds
            [ Org.sec1 1 (Org.text "Drawer in the node")
                (Org.db
                    [ Org.blank -- FIXME:
                    , Org.blank -- FIXME:
                    , Org.para1 $ Org.text "The blank lines above are considered a part of the drawer."
                    , Org.blank -- FIXME:
                    , Org.list Hyphened
                        [ Org.item1 $ Org.text "Item 1\n"
                        , (Org.item1 $ Org.text "Item 2")
                            # Org.idrawer1 "drawer" (Org.text "inside item 2")
                        , (Org.item1 $ Org.text "Item 3\n")
                        ]
                    ]
                )
                # Org.drawer1 "drawer" (Org.text "Text.")
            , Org.sec1 2 (Org.text "This is a headline")
                (Org.db
                    [ Org.para1 $ Org.text "Still outside the drawer"
                    , Org.bdrawer1 "drawername" $ Org.text "This is inside the drawer."
                    , Org.para1 $ Org.text "After the drawer."
                    , Org.blank
                    ]
                )
            , Org.sec 1
                [ Org.text "Heading title is a part of the headline element itself <BEGIN>"
                , Org.br, Org.br
                , Org.text "Text inside heading is considered a part of its CONTENTS and can", Org.br
                , Org.text "contain other elements recursively.  This paragraph only has CONTENTS,", Org.br
                , Org.text "no BEGIN, no END, and a BLANK line."
                ]
                (Org.db1 $ Org.para1 $ Org.text "This is the end of the heading, no END exists for headings."
                )
                # Org.drawer "drawer"
                    [ Org.text "The same works at the deeper levels, with this drawer having", Org.br
                    , Org.text "=:drawer:= line as BEGIN, this paragraph belonging to drawer CONTENTS,", Org.br
                    , Org.text "=:end:= representing END, and no BLANK after."
                    ]
            ]