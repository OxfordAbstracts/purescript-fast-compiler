module Org.Test.Test04g where


import Prelude (($))

import Data.Text.Format.Org.Types (OrgFile)
import Data.Text.Format.Org.Types (Interval(..), RepeaterMode(..), DelayMode(..)) as O
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.db
            [ Org.para1 $ Org.at $ Org.adatetime (Org.d 1997 11 3) (Org.t 19 15)
            , Org.para1 $ Org.diary "(diary-float t 4 2)"
            , Org.para1 $ Org.diary_r "(diary-float t 4 2)" $ Org.fromto_r (Org.t 12 0) (Org.t 14 0)
            , Org.para1 $ Org.range (Org.idate $ Org.d 2004 8 24) (Org.idate $ Org.d 2004 8 26)
            , Org.para1 $ Org.at $ Org.repeat O.FromToday 2 O.Day $ Org.adatetime (Org.d 2012 2 8) (Org.t 20 0)
            , Org.para1 $ Org.at $ Org.delay O.One 5 O.Day $ Org.repeat O.Single 1 O.Month $ Org.adate (Org.d 2030 10 5)
            , Org.para1 $ Org.at $ Org.rwith 2 O.Year $ Org.repeat O.FromToday 1 O.Year $ Org.adate (Org.d 2012 3 29)
            , Org.para1 $ Org.at $ Org.idate (Org.d 2024 9 5)
            , Org.para1 $ Org.at $ Org.idatetime (Org.d 1997 11 3) (Org.t 19 15)
            , Org.para1 $ Org.at $ Org.delay O.All 3 O.Week $ Org.repeat O.Jump 1 O.Hour $ Org.adate (Org.d 2010 2 22)
            , Org.blank
            -- , Org.para1 $ Org.text "clock: " <> Org.at (Org.idate $ Org.d 2024 10 12)
            , Org.para [ Org.text "clock: ", Org.at $ Org.idate $ Org.d 2024 10 12 ]
            , Org.para
                [ Org.text "CLOCK: "
                , Org.range
                    (Org.idatetime (Org.d 2019 3 25) (Org.t 10 49))
                    (Org.idatetime (Org.d 2019 3 25) (Org.t 11 31))
                , Org.text " "
                , Org.clock $ Org.t 0 42
                ]
            , Org.para
                [ Org.text "clock: "
                , Org.clock $ Org.t 12 30
                ]
            ]