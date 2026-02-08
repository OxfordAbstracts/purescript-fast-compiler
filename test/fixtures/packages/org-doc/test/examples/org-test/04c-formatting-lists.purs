module Org.Test.Test04c where


import Prelude (($), (#))

import Data.Text.Format.Org.Types (OrgFile, Check(..), ListType(..))
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.dbs
            [ Org.para1 $ Org.text "To buy:"
            , Org.list Numbered
                [ Org.item1 $ Org.text "Milk"
                , (Org.item1 $ Org.text "Eggs")
                    # Org.sub Hyphened
                        [ Org.item1 $ Org.text "Organic"
                        ]
                , (Org.item1 $ Org.text "Cheese")
                    # Org.sub Plussed
                        [ Org.item1 $ Org.text "Parmesan"
                        , Org.item1 $ Org.text "Mozzarella"
                        ]
                ]
            , Org.blank
            , Org.list Hyphened
                [ Org.check Uncheck $ Org.item1 $ Org.text "not started"
                , Org.check Halfcheck $ Org.item1 $ Org.text "in progress"
                , Org.check Check $ Org.item1 $ Org.text "complete"
                ]
            , Org.blank
            , Org.list Hyphened
                [ Org.tagi "fruits" $ Org.check Uncheck $ Org.item1 $ Org.text "get apples"
                , Org.tagi "veggies" $ Org.check Check $ Org.item1 $ Org.text "get carrots"
                ]
            , Org.blank
            , Org.list Alphed
                [ Org.item1 $ Org.text "First"
                , Org.item1 $ Org.text "Second"
                , Org.item1 $ Org.text "Third"
                , Org.item1 $ Org.text "Fourth"
                ]
            , Org.blank
            , Org.list Hyphened
                [ Org.item1 $ Org.text "item" ]
            , Org.list (NumberedFrom 3)
                [ Org.count 3 $ Org.item1 $ Org.text "set to three" ]
            , Org.list Plussed
                [ (Org.check Halfcheck $ Org.tagi "tag" $ Org.item1 $ Org.text "item contents")
                    # Org.sub Bulleted
                        [ Org.item1 $ Org.text "item, note whitespace in front" ]
                ]
            ]
            [ Org.sece1 1 $ Org.text "not an item, but heading - heading takes precedence"
            ]