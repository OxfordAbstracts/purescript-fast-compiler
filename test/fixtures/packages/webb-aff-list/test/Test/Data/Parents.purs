module Test.Data.Parents 
( module P
, sizeIs
, fakeParent
)
where

import Test.Prelude
import Webb.AffList.Data.Node.Parents

import Effect.Aff (Aff)
import Webb.AffList.Data.Node.Parent (class Parent, Parent_)
import Webb.AffList.Data.Node.Parent as Parent
import Webb.AffList.Data.Node.Parents as P
import Webb.Array as Array

sizeIs :: Parents -> Int -> Aff Unit
sizeIs arr n = do
  Array.size arr === n
  
newtype FakeParent = F Unit

instance Parent FakeParent where
  cancel _ = pure unit

fakeParent :: Parent_
fakeParent = Parent.wrap (F unit)