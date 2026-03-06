module Simple where

import Prelude (add, ($))
import Simple.Lib (class Cl, LibT(LibA, LibB), member, times2)

int :: Int
int = fn 1

fn :: Int -> Int
fn int = times2 $ int + increment
   where
   increment = 1

myAdd = add

infix 3 myAdd as +

data T = A | B

newtype I = I Int

fn2 :: T -> I
fn2 = case _ of
  A -> I 0
  B -> I 1

-- Format: line:col (name) => file start_line:start_col-end_line:end_col (0-indexed)
--
-- Line 2: import Prelude (add, ($))
-- 2:16 (add) => ../../packages/prelude/src/Data/Semiring.purs 44:2-44:5
-- 2:22 ($) => ../../packages/prelude/src/Data/Function.purs 47:0-47:5
--
-- Line 3: import Simple.Lib (class Cl, LibT(LibA, LibB), member, times2)
-- 3:25 (Cl) => Simple/Lib.purs 4:6-4:8
-- 3:29 (LibT) => Simple/Lib.purs 7:5-7:9
-- 3:34 (LibA) => Simple/Lib.purs 8:4-8:8
-- 3:40 (LibB) => Simple/Lib.purs 9:4-9:8
-- 3:47 (member) => Simple/Lib.purs 5:2-5:8
-- 3:55 (times2) => Simple/Lib.purs 11:0-11:6
--
-- Line 5: int :: Int
-- 5:7 (Int) => Prim (no source)
--
-- Line 6: int = fn 1
-- 6:6 (fn) => Simple.purs 9:0-13:0
--
-- Line 8: fn :: Int -> Int
-- 8:6 (Int) => Prim (no source)
-- 8:13 (Int) => Prim (no source)
--
-- Line 9: fn int = times2 $ int + increment
-- 9:9 (times2) => Simple/Lib.purs 11:0-11:6
-- 9:16 ($) => ../../packages/prelude/src/Data/Function.purs 47:0-47:5
-- 9:18 (int) => Simple.purs 9:3-9:6
-- 9:22 (+) => Simple.purs 15:0-15:18
-- 9:24 (increment) => Simple.purs 11:3-11:12
--
-- Line 13: myAdd = add
-- 13:8 (add) => ../../packages/prelude/src/Data/Semiring.purs 44:2-44:5
--
-- Line 19: newtype I = I Int
-- 19:14 (Int) => Prim (no source)
--
-- Line 21: fn2 :: T -> I
-- 21:7 (T) => Simple.purs 17:0-17:14
-- 21:12 (I) => Simple.purs 19:0-19:17
--
-- Line 23: A -> I 0
-- 23:2 (A) => Simple.purs 17:9-17:10
-- 23:7 (I) => Simple.purs 19:0-19:17
--
-- Line 24: B -> I 1
-- 24:2 (B) => Simple.purs 17:13-17:14
-- 24:7 (I) => Simple.purs 19:0-19:17
