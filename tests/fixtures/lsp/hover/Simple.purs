module Simple where

import Simple.Lib (times2)

-- | The answer to everything
x = 42

fn :: Int -> Int
fn n = times2 n

data Color = Red | Green | Blue

data Box a = MkBox a

boxed = MkBox 42

colorFn c = case c of
  Red -> 1
  Green -> 2
  Blue -> 3

-- Format: line:col (name) => hover: <expected_type_substring>
-- Use "null" for expected null result
-- Use "doc: <text>" to also check doc-comment content
--
-- Line 5: x = 42
-- 5:0 (x) => hover: Int | doc: The answer to everything
--
-- Line 7: fn :: Int -> Int
-- 7:0 (fn) => hover: (Int -> Int)
--
-- Line 8: fn n = times2 n
-- 8:7 (times2) => hover: times2
--
-- Line 10: data Color = Red | Green | Blue
-- 10:5 (Color) => hover: Type
--
-- Line 14: boxed = MkBox 42
-- 14:0 (boxed) => hover: (Box Int)
--
-- Line 16: colorFn c = case c of
-- 16:0 (colorFn) => hover: (Color -> Int)
--
-- Line 1: empty line
-- 1:0 (ws) => hover: null
