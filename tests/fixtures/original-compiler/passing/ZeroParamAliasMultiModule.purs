module Main where

import Data as D
import Types (Update)
import Consumer (consume)

-- Multiple modules import the same zero-param alias that
-- references a qualified data type with the same name.
-- All modules must expand the alias correctly.
make :: Update
make = D.Update 42 "hello"

test :: Int
test = consume make
