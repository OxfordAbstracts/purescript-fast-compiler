module ConstraintOnlyClassImport where

import ConstraintOnlyClassImport.Dep (class Item)

useItem :: forall a. Item a => a -> a
useItem x = x
