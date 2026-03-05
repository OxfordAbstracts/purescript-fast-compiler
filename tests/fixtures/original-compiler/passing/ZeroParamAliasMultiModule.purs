module Main where

import Data as D
import Types (A)
import Consumer (consume)

-- Multiple modules import the same zero-param alias that
-- references a qualified data type with the same name.
-- All modules must expand the alias correctly.
make :: A
make = D.A 42 "hello"

test :: Int
test = consume make
