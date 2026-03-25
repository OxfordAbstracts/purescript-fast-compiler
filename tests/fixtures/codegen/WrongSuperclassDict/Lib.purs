module Lib where

-- Superclass: MySup with an accessor
class MySup a where
  supMethod :: a -> String

-- Subclass: MySub extends MySup, with MySup0 accessor
class MySup a <= MySub a where
  subMethod :: a -> Int

-- A concrete type
data MyThing = MyThing

-- Direct instance for MySup MyThing
instance mySupMyThing :: MySup MyThing where
  supMethod _ = "sup"

-- Direct instance for MySub MyThing
instance mySubMyThing :: MySub MyThing where
  subMethod _ = 42

-- Function that takes ONLY MySup constraint
-- At call site, codegen should pass mySupMyThing, NOT mySubMyThing
useSup :: forall a. MySup a => a -> String
useSup a = supMethod a
