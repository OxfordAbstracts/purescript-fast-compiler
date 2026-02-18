module App where

import MyLib (class MyAppend, (<>))

joined :: forall a. MyAppend a => a -> a -> a
joined x y = x <> y
