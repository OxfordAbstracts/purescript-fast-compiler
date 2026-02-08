module Org.Test.Test04e where


import Prelude (($))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.db
            [ Org.para1 $ Org.fn "LABEL"
            , Org.para1 $ Org.fndef "LABEL" "DEFINITION"
            , Org.para1 $ Org.fndef' "DEFINITION"
            , Org.blank
            , Org.para
                [ Org.text "Some text with footnote "
                , Org.fn "1"
                , Org.text " inside. Also an "
                , Org.fndef "inline" "Inline footnote"
                , Org.text " somehow appeared here."
                , Org.br
                , Org.text "And a footnote "
                , Org.fndef' "only with definition"
                , Org.text ", right away."
                ]
            , Org.blank
            , Org.blank
            , Org.fn_ "1" [ Org.text "A short footnote." ]
            , Org.blank
            , Org.fn_ "2" [ Org.text "This is a longer footnote.", Org.br, Org.text "It even contains a single blank line." ]
            ]