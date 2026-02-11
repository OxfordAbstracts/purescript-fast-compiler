module Webb.Directory.Data.Stack where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (class Newtype, unwrap, wrap)
import Webb.Directory.Data.Absolute (AbsolutePath)



newtype Stack = St (Array AbsolutePath)

type Path = String

derive newtype instance Eq Stack
derive newtype instance Ord Stack
derive newtype instance Show Stack
derive instance Newtype Stack _

emptyStack :: Stack
emptyStack = wrap []

-- Push an absolute path.
push :: AbsolutePath -> Stack -> Stack
push s stack = stack # unwrap >>> flip Array.snoc s >>> wrap

pop :: Stack -> Stack
pop = unwrap >>> Array.dropEnd 1 >>> wrap

-- Pops to the first item in the stack, if it exists
popToFirst :: Stack -> Stack
popToFirst stack = case peek stack of
  Nothing -> stack
  Just _ -> stack # unwrap >>> Array.take 1 >>> wrap

peek :: Stack -> Maybe AbsolutePath
peek = unwrap >>> Array.last

replace :: AbsolutePath -> Stack -> Stack
replace s = pop >>> push s

-- All paths in the stack, from bottom (first) to top (last)
paths :: Stack -> Array AbsolutePath
paths = unwrap

-- Is the absolute path in the stack?
contains :: AbsolutePath -> Stack -> Boolean
contains path stack = let 
  array = unwrap stack
  in isJust $ Array.find (_ == path) array

size :: Stack -> Int
size = unwrap >>> Array.length

isEmpty :: Stack -> Boolean
isEmpty = size >>> (_ <= 0)