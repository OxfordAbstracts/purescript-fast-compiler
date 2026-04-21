module Main where

import Prelude
import Effect.Console (log)

data Either a b = Left a | Right b

instance functorEither :: Functor (Either a) where
  map _ (Left x) = ?test
  map f (Right y) = Right (f y)

main = log "Done"
