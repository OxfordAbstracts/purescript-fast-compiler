module Test.Internal.ListFiber where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Webb.AffList.Internal.ListFiber as LFiber
import Webb.AffList.Internal.Node as Node
import Webb.Array as Array


type ListFiberProps = Unit

new :: Array Int -> Aff (LFiber.ListFiber Int)
new ints = do 
  node <- Node.newNode
  Node.setProgram node (loop node ints)
  
  fiber <- LFiber.newListFiber node
  pure fiber
  where
  loop node xs = do
    case Array.uncons xs of
      Just s -> do
        void $ Node.send node s.head
        loop node s.tail
      Nothing -> do 
        pure unit
