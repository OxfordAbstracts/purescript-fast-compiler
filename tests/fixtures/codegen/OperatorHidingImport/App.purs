module App where

import MyLib hiding (unused)

joined :: forall a. MyAppend a => a -> a -> a
joined x y = x <> y
