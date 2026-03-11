module Main where

import ConstraintOnlyClassImport.Dep (class Item)
import Effect.Console (log)

useItem :: forall a. Item a => a -> a
useItem x = x

main = log "Done"
