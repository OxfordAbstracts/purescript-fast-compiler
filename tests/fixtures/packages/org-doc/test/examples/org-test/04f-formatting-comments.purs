module Org.Test.Test04f where


import Prelude (($), (<$>))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
    $ Org.dbs
        [ Org.lcomment [ "A line comment" ]
        , Org.blank
        , Org.para [ Org.text "Example of an ", Org.icomment "inline", Org.text " comment." ]
        , Org.blank
        , Org.para [ Org.text "Inline comments are used for end of line comments. ", Org.icomment "~#~ won't\nwork", Org.text " Since # only only works if preceeded by a newline follow by", Org.br, Org.text "whitespace." ]
        , Org.blank
        , Org.bcomment
            [ "This is a block comment."
            , "It can span multiple line."
            , "As well as other markup."
            , "#+BEGIN_SRC emacs-lisp"
            , "(+ 1 2)"
            , "#+END_SRC"
            ]
        , Org.blank
        ]
        [ Org.sec1 1 (Org.text "A top level heading")
            $ Org.ds
            [ Org.comment
                $ Org.sec1 2 (Org.text "This section and subsections are commented out")
                    $ Org.ds1
                        $ Org.sec 3 [ Org.text "This heading inherits the ", Org.v "COMMENT", Org.text " keyword" ]
                        $ Org.db1 $ Org.para1 $ Org.text "This text is commented out"
            , Org.sec1 2 (Org.text "This heading is not commented")
                $ Org.db
                    [ Org.para1 $ Org.text "This text will be exported and code blocks will run"
                    , Org.blank
                    , Org.bcomment -- FIXME: first line should not be indented
                        [ "A comment is taken verbatim, with this text not parsed recursively and"
                        , "considered a part of the comment block element itself."
                        , "=#+BEGIN_COMMENT= is BEGIN, =#+END_COMMENT= - END, and VALUE is this"
                        , "text."
                        ]
                    ]
            ]
        ]