module Test.Internal.Node.Parents where

import Test.Prelude

import Data.Newtype (class Newtype, unwrap)
import Data.Traversable (sequence)
import Effect.Aff (Aff)
import Webb.AffList.Data.Node.Parent as Parent
import Webb.AffList.Internal.Node.Parents as Parents
import Webb.AffList.Internal.Node.State as State
import Webb.State.Prelude (ShowRef, aread, newShowRef)


type PProps = Unit
type ParentProps = Unit


newtype FakeParent = F (ShowRef Boolean)

derive instance Newtype FakeParent _

instance Parent.Parent FakeParent where
  cancel (F ref) = ref := false

new :: forall a. Array Boolean -> Aff (Parents.Parents a)
new bools = do 
  state <- State.new
  setFakeParents state bools
  pure state

newFakeParent :: Aff FakeParent
newFakeParent = do 
  ref <- newShowRef true
  pure $ F ref
  
setFakeParents :: forall a. State.NodeState a -> Array Boolean -> Aff Unit
setFakeParents state bools = do 
  parents <- mkParents
  state.parents := parents
  where
  mkParents = do
    refs <- sequence (newShowRef <$> bools)
    pure $ (Parent.wrap <<< F) <$> refs
  
fakeParents :: forall a. State.NodeState a -> Aff (Array Boolean)
fakeParents state = do 
  arr <- Parents.parents state
  let fakes = (Parent.unsafeRecover <$> arr) :: Array FakeParent 
  let refs = unwrap <$> fakes
  actuals <- sequence (aread <$> refs)
  pure actuals

parentsAre :: forall a. Parents.Parents a -> Array Boolean -> Aff Unit
parentsAre state bools = do 
  actuals <- fakeParents state
  actuals === bools

countIs :: forall a. Parents.Parents a -> Int -> Aff Unit
countIs state n = do 
  i <- Parents.parentCount state
  i === n