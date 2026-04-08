module Simple where

import Prelude (add, ($))
import Simple.Lib (class Cl, LibT(LibA, LibB), member, times2)
import Simple.Lib as Lib

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

qualUse = Lib.times2 42

-- Format: line:col (name) => file start_line:start_col-end_line:end_col (0-indexed)
--
-- Line 2: import Prelude (add, ($))
-- 2:16 (add) => ../../packages/prelude/src/Data/Semiring.purs 44:2-44:5
-- 2:22 ($) => ../../packages/prelude/src/Data/Function.purs 47:0-47:5
--
-- Line 3: import Simple.Lib (class Cl, LibT(LibA, LibB), member, times2)
-- 3:7 (Simple.Lib) => Simple/Lib.purs 0:0-0:0
-- 3:25 (Cl) => Simple/Lib.purs 4:6-4:8
-- 3:29 (LibT) => Simple/Lib.purs 7:5-7:9
-- 3:34 (LibA) => Simple/Lib.purs 8:4-8:8
-- 3:40 (LibB) => Simple/Lib.purs 9:4-9:8
-- 3:47 (member) => Simple/Lib.purs 5:2-5:8
-- 3:55 (times2) => Simple/Lib.purs 11:0-11:6
--
-- Line 4: import Simple.Lib as Lib — goto module name
-- 4:7 (Simple.Lib) => Simple/Lib.purs 0:0-0:0
--
-- Line 6: int :: Int
-- 6:7 (Int) => Prim (no source)
--
-- Line 7: int = fn 1
-- 7:6 (fn) => Simple.purs 10:0-14:0
--
-- Line 9: fn :: Int -> Int
-- 9:6 (Int) => Prim (no source)
-- 9:13 (Int) => Prim (no source)
--
-- Line 10: fn int = times2 $ int + increment
-- 10:9 (times2) => Simple/Lib.purs 11:0-11:6
-- 10:16 ($) => ../../packages/prelude/src/Data/Function.purs 47:0-47:5
-- 10:18 (int) => Simple.purs 10:3-10:6
-- 10:22 (+) => Simple.purs 16:0-16:18
-- 10:24 (increment) => Simple.purs 12:3-12:12
--
-- Line 14: myAdd = add
-- 14:8 (add) => ../../packages/prelude/src/Data/Semiring.purs 44:2-44:5
--
-- Line 20: newtype I = I Int
-- 20:14 (Int) => Prim (no source)
--
-- Line 22: fn2 :: T -> I
-- 22:7 (T) => Simple.purs 18:0-18:14
-- 22:12 (I) => Simple.purs 20:0-20:17
--
-- Line 24: A -> I 0
-- 24:2 (A) => Simple.purs 18:9-18:10
-- 24:7 (I) => Simple.purs 20:0-20:17
--
-- Line 25: B -> I 1
-- 25:2 (B) => Simple.purs 18:13-18:14
-- 25:7 (I) => Simple.purs 20:0-20:17
--
-- Line 27: qualUse = Lib.times2 42 — qualified via import as Lib
-- 27:14 (times2) => Simple/Lib.purs 11:0-11:6
