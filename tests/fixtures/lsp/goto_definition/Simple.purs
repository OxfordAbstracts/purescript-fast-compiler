module Simple where

import Prelude (add, ($))
import Simple.Lib (class Cl, LibT(LibA, LibB), member, times2)

int :: Int
int = fn 1

fn :: Int -> Int
fn int = times2 ($) int + increment
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

-- Format: line:col => file start_line:start_col-end_line:end_col (0-indexed)
-- Prim types have no source location (go-to-def returns null)
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
-- 9:16 ($) => unresolved (not imported)
-- 9:18 (int) => Simple.purs 9:3-9:6 (fn param)
-- 9:22 (+) => Simple.purs 15:0-15:18 (local fixity decl)
-- 9:24 (increment) => Simple.purs 11:3-11:12 (where binding)
--
-- Line 13: myAdd = add
-- 13:8 (add) => Prelude (imported, no local source)
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
