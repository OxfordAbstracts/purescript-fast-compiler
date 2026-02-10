module Org.Test.Test04h where


import Prelude (($), (#))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Types (ListType(..))
import Data.Text.Format.Org.Construct as Org
import Data.Text.Format.Org.Property as Org


test :: OrgFile
test =
    Org.f
        $ Org.ds
            [ Org.sec1 1 (Org.text "Node Properties") Org.emptyDoc
                # Org.wprop (Org.prop "NAME" "VALUE")
                # Org.wprop (Org.propn "NAME")
                # Org.wprop (Org.propapp "NAME" "VALUE")
                # Org.wprop (Org.propappn "NAME")
            , Org.sec1 1 (Org.text "Heading")
                    (Org.db
                        [ Org.blank
                        , Org.with_kws
                            [ Org.kw "KEY" "VALUE"
                            , Org.kwopt "KEY" "OPTVAL" "VALUE"
                            , Org.kw "attr_BACKEND" "VALUE"
                            ]
                            $ Org.para1 $ Org.text "Some content"
                        , Org.blank
                        , Org.with_kws
                            [ Org.kw "name" "image-name"
                            , Org.kw "caption" "This is a caption for"
                            , Org.kw "caption" "the image linked below"
                            ]
                            $ Org.para1 $ Org.img_ $ Org.iloc "some/image.png"
                        ]
                    )
                # Org.wprop (Org.prop "CUSTOM_ID" "someid")
            ]