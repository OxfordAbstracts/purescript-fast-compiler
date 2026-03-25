module Test where

import Lib

-- This should use mySupMyThing (the direct MySup instance),
-- NOT mySubMyThing (which has MySup0 accessor to get MySup)
-- If codegen wrongly passes mySubMyThing, it would try to call
-- subMethod.supMethod which would fail at runtime
test = useSup MyThing
-- TEST: "sup"
