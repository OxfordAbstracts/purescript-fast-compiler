module ShowArrayBug where
-- TEST: "[1,2,3]"

import Data.Show (class Show, show)

-- Direct reproduction of the spec bug: Show (Array Int) should use showArray(showInt)
-- but our compiler may pass showInt directly where showArray(showInt) is needed.

showIt :: forall f a. Show a => Show (f a) => f a -> String
showIt x = show x

test :: String
test = showIt [1, 2, 3]
