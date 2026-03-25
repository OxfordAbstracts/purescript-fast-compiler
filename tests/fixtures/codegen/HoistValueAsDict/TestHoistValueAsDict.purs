module TestHoistValueAsDict where

import Prelude (class Semigroup, class Monoid, (<>), mempty)
import MyLib (myConcat)
import Separator (mySep)

-- Bug 4 (tidy-codegen): dict dropped, value arg used in its place.
-- myConcat needs Monoid dict first, then sep, a, b.
-- If dict is dropped: myConcat(mySep)(a)(b) instead of myConcat(monoidString)(mySep)(a)(b).

-- Inside a function body so the hoister can operate at depth > 0.
wrapper :: String -> String
wrapper _ = myConcat mySep "hello" "world"

test :: String
test = wrapper ""
-- TEST: "hello-world"
