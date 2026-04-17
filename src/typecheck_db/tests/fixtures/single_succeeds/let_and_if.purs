module Test.LetAndIf where

-- `let` introduces a local binding; the body refers to it.
five :: Int
five =
  let
    x = 5
  in x

-- Nested let with multiple bindings.
sumXY :: Int
sumXY =
  let
    x = 1
    y = 2
  in x

-- if-then-else — both branches must unify to the same result type.
pickInt :: Boolean -> Int
pickInt cond = if cond then 1 else 2
