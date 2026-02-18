module App where

import MyPrelude (class MyAppend, (<>))

joined :: forall a. MyAppend a => a -> a -> a
joined x y = x <> y
