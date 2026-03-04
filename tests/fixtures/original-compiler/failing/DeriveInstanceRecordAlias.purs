-- @shouldFailWith InvalidInstanceHead
module Main where

import Prelude

type MyRec r = { x :: Int | r }

instance showMyRec :: Show (MyRec r) where
  show _ = ""
