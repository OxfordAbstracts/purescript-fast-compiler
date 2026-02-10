module Bookhound.Utils.List where

import Data.List (List, (:))

hasNone :: forall a. List a -> Boolean
hasNone (_ : _) = false
hasNone _ = true

hasSome :: forall a. List a -> Boolean
hasSome (_ : _) = true
hasSome _ = false

hasMultiple :: forall a. List a -> Boolean
hasMultiple (_ : _ : _) = true
hasMultiple _ = false
