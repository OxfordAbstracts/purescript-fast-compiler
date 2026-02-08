module Webb.AffList.Data.Node.Parents where

import Prelude

import Webb.AffList.Data.Node.Parent (class Parent, Parent_)
import Webb.AffList.Data.Node.Parent as Parent
import Webb.Array as Array



type Parents = Array Parent_

empty :: Parents 
empty = []

addParent :: forall a. Parent a => a -> Parents -> Parents
addParent a = Array.addLast (Parent.wrap a)

size :: Parents -> Int
size = Array.size

isEmpty :: Parents -> Boolean
isEmpty = Array.isEmpty
