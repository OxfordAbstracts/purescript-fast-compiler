module Org.Test.Test04b where


import Prelude (($))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.db
            [ Org.para
                [ Org.text "To markup text in Org, simply surround it with one or more marker characters."
                , Org.br, Org.b "Bold", Org.text ", ", Org.i "italic", Org.text " and ", Org.u "underline", Org.text " are fairly intuitive, and the ability to use", Org.br
                , Org.s "strikethrough", Org.text " is a plus.  You can ", Org.marked (Org.both Org.bold $ Org.both Org.italic Org.under) "combine", Org.text " the basic markup in any", Org.br
                , Org.text "order, however ", Org.ic "code", Org.text " and ", Org.v "verbatim", Org.text " need to be the ", Org.marked (Org.both Org.icode $ Org.both Org.under Org.bold) "inner-most", Org.text " markers", Org.br
                , Org.text "if they are present since their contents are interpreted ", Org.v "_literally_", Org.text "."
                ]
            , Org.blank
            , Org.para
                [ Org.to (Org.rem "https://orgmode.org") "a nice website", Org.br
                , Org.ref (Org.loc "~/Pictures/dank-meme.png"), Org.br
                , Org.to (Org.head "earlier heading") "an earlier heading in the document", Org.br
                ]
            , Org.para1 $ Org.img_ (Org.irem "https://upload.wikimedia.org/wikipedia/commons/5/5d/Konigsberg_bridges.png")
            , Org.blank
            , Org.example [ Org.text "monospace" ]
            , Org.blank
            , Org.codeIn "emacs-lisp" "(message \"Hello world\")"
            , Org.blank
            , Org.quote [ Org.text "Everything should be made as simple as possible,\nbut not any simpler ---Albert Einstein" ]
            , Org.blank
            , Org.hr
            , Org.blank
            , Org.fw [ Org.text "Some fixed-width text here", Org.br, Org.text "Containing several lines", Org.br, Org.text "Is it understandable?" ]
            ]

-- TODO: horizontal lines + fixed width area
-- TODO: multiple line comments