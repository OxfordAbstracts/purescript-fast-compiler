module TestInitCycle where

import MyDecode
import MyDecoders

test = case (myDecode "hello" :: MyResult String) of
  Ok s -> s
  Fail _ -> "fail"

-- TEST: "hello"
