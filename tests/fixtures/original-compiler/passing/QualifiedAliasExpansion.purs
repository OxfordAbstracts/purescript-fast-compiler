module Main where

import Lib as L

-- Qualified alias should expand correctly
x :: L.Alias
x = 42

-- Qualified record alias should also work
y :: L.Rec
y = { x: 1, y: "hello" }
