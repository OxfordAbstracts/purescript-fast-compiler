module Org.Test.Test06a where


import Prelude (($), (#))

import Data.Text.Format.Org.Types (OrgFile, ListType(..))
import Data.Text.Format.Org.Construct as Org
import Data.Text.Format.Org.Property as P


test :: OrgFile
test =
    Org.f
        $ Org.ds
            [ Org.sec1 1 (Org.text "Node properties")
                    (Org.db
                        [ Org.blank -- FIXME:
                        , Org.para1 $ Org.text "The blank lines above are considered a part of a drawer"
                        , Org.list Hyphened
                            [ Org.item1 $ Org.text "Item 1\n"
                            , (Org.item1 $ Org.text "Item 2\n")
                                # Org.idrawer1 "drawer" (Org.text "inside item 2")
                            ]
                        ]
                    )
                # Org.wprop (P.prop "NAME" "VALUE")
                # Org.wprop (P.propn "NAME")
                # Org.wprop (P.propapp "NAME" "VALUE")
                # Org.wprop (P.propappn "NAME")
                # Org.drawer1 "drawer" (Org.text "Text.")
            , Org.sec 1
                    [ Org.text "Heading title is a part of the headline element itself <BEGIN>"
                    , Org.br, Org.br
                    , Org.text "Text inside heading is considered a part of its CONTENTS and can"
                    , Org.text "contain other elements recursively.  This paragraph only has CONTENTS,"
                    , Org.text "no BEGIN, no END, and a BLANK line."
                    ]
                (Org.db1 $ Org.para1 $ Org.text "This is the end of the heading, no END exists for headings."
                )
                # Org.drawer "drawer"
                    [ Org.text "The same works at the deeper levels, with this drawer having", Org.br
                    , Org.text "=:drawer:= line as BEGIN, this paragraph belonging to drawer CONTENTS,"
                    , Org.text "=:end:= representing END, and no BLANK after."
                    ]
            , Org.sec1 1 (Org.text "Heading")
                    (Org.db
                        [ Org.with_kws
                            [ Org.kw "KEY" "VALUE"
                            , Org.kwopt "KEY" "OPTVAL" "VALUE"
                            , Org.kw "attr_BACKEND" "VALUE"
                            ]
                            Org.blank
                        , Org.with_kws
                            [ Org.kw "name" "image-name"
                            , Org.kw "caption" "This is a caption for"
                            , Org.kw "caption" "the image linked below"
                            ]
                            $ Org.para1 $ Org.img_ $ Org.iloc "some/image.png"
                        ]
                    )
                # Org.wprop (P.prop "CUSTOM_ID" "someid")
            ]