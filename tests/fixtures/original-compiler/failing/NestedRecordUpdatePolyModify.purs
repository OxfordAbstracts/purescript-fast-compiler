-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdatePolyModify where

import Prelude

-- Simulate H.modify_ :: forall s m. MonadState s m => (s -> s) -> m Unit
-- The key: `s` is constrained by MonadState, not concretely known at the
-- record update site. The type error should still be caught when `s` is
-- resolved to State.

class MonadState s m | m -> s where
  modify_ :: (s -> s) -> m Unit

type Inner = { fields :: { x :: Int }, other :: Boolean }
type State = { context :: Inner, count :: Int, flag :: Boolean }

data MyM a = MyM a

instance MonadState State MyM where
  modify_ _ = MyM unit

test :: MyM Unit
test = modify_ \st ->
  let
    newFlag = st.flag
  in
    st
      { flag = newFlag
      , context { fields = "Not a record" }
      }
