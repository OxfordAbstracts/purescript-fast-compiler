module Org.Test.Test04a where


import Prelude (($))

import Data.Text.Format.Org.Types (OrgFile, Todo(..))
import Data.Text.Format.Org.Construct as Org


test :: OrgFile
test =
    Org.f
        $ Org.ds
            [ Org.sec1 1 (Org.text "Welcome to Org-mode")
                $ Org.ssec1 2 (Org.text "Sub-heading")
                    $ Org.db1 $ Org.para [ Org.text "Each extra ~*~ increases the depth by one level.", Org.br ]
            , Org.set Todo $ Org.sec1 1 (Org.text "Promulgate Org to the world")
                $ Org.ds1
                    $ Org.set Todo $ Org.sece1 2 $ Org.text "Create a quickstart guide"
            ]