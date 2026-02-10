-- | Provides an FFI bindings for the
-- | [Enzyme](https://enzymejs.github.io/enzyme/) library. This is a pretty thin
-- | wrapper around Enzyme with a few convenience functions added. For a
-- | convenient API, use `Elmish.Enzyme` instead.
module Elmish.Enzyme.Foreign
  ( Wrapper, NodeMultiplicity, SingleNode, ManyNodes
  , configure
  , mount
  , mountComponent
  , at
  , childAt
  , children
  , count
  , debug
  , exists
  , find
  , forEach
  , is
  , length
  , name
  , parent
  , prop
  , simulate
  , simulate'
  , simulateCustom'
  , state
  , text
  , toArray
  , unmount
  , unsafeSetState
  , update
  ) where

import Prelude

import Data.Array ((..))
import Data.Function.Uncurried (Fn2, runFn2)
import Data.Traversable (for, for_)
import Effect (Effect)
import Effect.Aff (Milliseconds(..), delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Aff.Compat (EffectFn2, EffectFn3, EffectFnAff, fromEffectFnAff, runEffectFn2, runEffectFn3)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Uncurried (EffectFn1, runEffectFn1)
import Elmish (ComponentDef, ReactElement, construct)
import Elmish.Enzyme.Adapter (Adapter)
import Foreign (Foreign, unsafeToForeign)

data NodeMultiplicity
foreign import data SingleNode :: NodeMultiplicity
foreign import data ManyNodes :: NodeMultiplicity

data Wrapper (w :: NodeMultiplicity)

-- | Configures the correct Enzyme adapter. Called once in the main spec.
configure :: Adapter -> Effect Unit
configure = runEffectFn1 configure_

-- | Fully mounts a `ReactElement` and returns a `Wrapper`.
-- | See https://enzymejs.github.io/enzyme/docs/api/shallow.html for more info.
mount :: forall m. MonadEffect m => ReactElement -> m (Wrapper SingleNode)
mount =
  liftEffect <<< runEffectFn1 mount_

-- | A convenience function for creating a full wrapper from a `ComponentDef`
-- | rather than a `ReactElement`. This also adds a `delay (Milliseconds 0.0)`
-- | to allow any effects in `def.init` to run.
mountComponent :: forall m msg state. MonadAff m => ComponentDef msg state -> m (Wrapper SingleNode)
mountComponent def = do
  wrapper <- liftEffect $ mount =<< construct def
  liftAff $ delay (Milliseconds 0.0)
  update wrapper
  pure wrapper

-- | A `Wrapper` can wrap multiple DOM nodes. This function returns the node at
-- | the given index. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/at.html for more
-- | info.
at :: forall m. MonadEffect m => Int -> Wrapper ManyNodes -> m (Wrapper SingleNode)
at idx w = liftEffect $ runEffectFn2 at_ idx w

-- | Returns all elements contained in the given `Wrapper` as an array.
toArray :: forall m. MonadEffect m => Wrapper ManyNodes -> m (Array (Wrapper SingleNode))
toArray e = for (0 .. (length e - 1)) \idx -> at idx e

-- | Runs the given action for every element contained in the given
-- | `Wrapper` as an array.
forEach :: forall m. MonadEffect m => (Wrapper SingleNode -> m Unit) -> Wrapper ManyNodes -> m Unit
forEach f e = for_ (0 .. (length e - 1)) \idx -> at idx e >>= f

-- | Prints the shallow DOM tree up to any nested React components.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/debug.html
-- | for more info.
debug :: forall m n. MonadEffect m => Wrapper n -> m String
debug = liftEffect <<< runEffectFn1 debug_

-- | Returns a `Boolean` indicating whether a given selector exists within the
-- | given `Wrapper`.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/exists.html
-- | for more info.
exists :: forall m n. MonadEffect m => String -> Wrapper n -> m Boolean
exists selector w = liftEffect $ runEffectFn2 exists_ selector w

-- | Finds all elements with the given selector within the given
-- | `Wrapper`. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/find.html for
-- | more info.
find :: forall m n. MonadEffect m => String -> Wrapper n -> m (Wrapper ManyNodes)
find selector w = liftEffect $ runEffectFn2 find_ selector w

-- | Returns parent of the given `Wrapper`. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/parent.html for
-- | more info.
parent :: forall m n. MonadEffect m => Wrapper n -> m (Wrapper n)
parent w = liftEffect $ runEffectFn1 parent_ w

-- | Returns the child nodes of the given `Wrapper`. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/children.html ffor
-- | more info.
children :: forall m n. MonadEffect m => Wrapper n -> m (Wrapper ManyNodes)
children w = liftEffect $ runEffectFn1 children_ w

-- | Returns the child node at index `idx` of the given `Wrapper`. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/childAt.html ffor
-- | more info.
childAt :: forall m n. MonadEffect m => Int -> Wrapper n -> m (Wrapper SingleNode)
childAt idx w = liftEffect $ runEffectFn2 childAt_ idx w

-- | Returns a `Boolean` indicating whether the given `Wrapper` matches
-- | the given selector.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/is.html
-- | for more info.
is :: forall m. MonadEffect m => String -> (Wrapper SingleNode) -> m Boolean
is selector w = liftEffect $ runEffectFn2 is_ selector w

-- | Returns number of elements in a given wrapper
foreign import length :: Wrapper ManyNodes -> Int

-- | Returns the value of a `Wrapper`’s prop with a certain key.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/prop.html
-- | for more info.
prop :: forall a m. MonadEffect m => String -> Wrapper SingleNode -> m a
prop selector w = liftEffect $ runEffectFn2 prop_ selector w

-- | Sets the state of the given `Wrapper`. This is asynchronous, so runs
-- | in a `MonadAff`. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/setState.html for
-- | more info.
-- |
-- | NOTE: this is a type-unsafe operation. There is no check to make sure the
-- | state being set here has the type of the actual state the component in
-- | question is using.
unsafeSetState :: forall state m. MonadAff m => state -> Wrapper SingleNode -> m Unit
unsafeSetState newState =
  liftAff <<< fromEffectFnAff <<< runFn2 unsafeSetState_ newState

-- | A convenience function for calling `simulate'` without an `event` arg.
simulate :: forall m. MonadEffect m => String -> Wrapper SingleNode -> m Unit
simulate eventType =
  simulate' eventType {}

-- | Simulates a certain event type on a given `Wrapper`. The event argument
-- | is a record that gets merged with a simulated React synthetic event before
-- | being passed to the component’s event handler. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/simulate.html for
-- | more info.

-- | NOTE: This doesn’t actually emit an event, but just triggers the event
-- | handler on the wrapper.
-- |
-- | NOTE 2: This function only works for native HTML elements. For emitting
-- | events on custom React components, use `simulateCustom`.
simulate' :: forall m r. MonadEffect m => String -> Record r -> Wrapper SingleNode -> m Unit
simulate' eventType event =
  liftEffect <<< runEffectFn3 simulate_ eventType (unsafeToForeign event)

-- | Simulates an event on a custom React component (i.e. not an HTML element).
-- | For reasons to complicated to discuss here, the regular `simulate` doesn't
-- | work on custom components, so we provide this workaround.
-- |
-- | NOTE: the second parameter is passed to the event handler without any
-- | checks whatsoever. This is, of course, not type-safe, but it is in line
-- | with what the event handler should expect anyway: after all, the underlying
-- | JavaScript component may pass anything at all as event argument.
simulateCustom' :: forall m a. MonadEffect m => String -> a -> Wrapper SingleNode -> m Unit
simulateCustom' eventType event =
  liftEffect <<< runEffectFn3 simulateCustom_ eventType (unsafeToForeign event)

-- | Returns the state of the given `Wrapper`.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/state.html
-- | for more info.
state :: forall m. MonadEffect m => Wrapper SingleNode -> m Foreign
state = liftEffect <<< runEffectFn1 state_

-- | Returns the text within the given `Wrapper`.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/text.html
-- | for more info.
text :: forall m. MonadEffect m => Wrapper SingleNode -> m String
text = liftEffect <<< runEffectFn1 text_

-- | Returns tag name of the given `Wrapper`.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/name.html
-- | for more info.
name :: forall m. MonadEffect m => Wrapper SingleNode -> m String
name = liftEffect <<< runEffectFn1 name_

-- | Returns the number of times a given selector appears within a wrapper.
count :: forall m n. MonadEffect m => String -> Wrapper n -> m Int
count selector wrapper = do
  length <$> find selector wrapper

-- | Unmounts a fully mounted component.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/unmount.html
-- | for more info.
unmount :: forall m. MonadEffect m => Wrapper SingleNode -> m Unit
unmount =
  liftEffect <<< runEffectFn1 unmount_

-- | Updates the given `Wrapper` to reflect the latest state. Call this
-- | function whenever you think there could be an async change of state that
-- | caused a re-render. For some reason, Enzyme won't pick up the changes
-- | automatically. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/update.html for
-- | more info.
update :: forall m n. MonadEffect m => Wrapper n -> m Unit
update = liftEffect <<< runEffectFn1 update_

foreign import configure_ :: EffectFn1 Adapter Unit

foreign import mount_ :: EffectFn1 ReactElement (Wrapper SingleNode)

foreign import at_ :: EffectFn2 Int (Wrapper ManyNodes) (Wrapper SingleNode)

foreign import debug_ :: forall n. EffectFn1 (Wrapper n) String

foreign import exists_ :: forall n. EffectFn2 String (Wrapper n) Boolean

foreign import find_ :: forall n. EffectFn2 String (Wrapper n) (Wrapper ManyNodes)

foreign import parent_ :: forall n. EffectFn1 (Wrapper n) (Wrapper n)

foreign import children_ :: forall n. EffectFn1 (Wrapper n) (Wrapper ManyNodes)

foreign import childAt_ :: forall n. EffectFn2 Int (Wrapper n) (Wrapper SingleNode)

foreign import is_ :: EffectFn2 String (Wrapper SingleNode) Boolean

foreign import prop_ :: forall a. EffectFn2 String (Wrapper SingleNode) a

foreign import unsafeSetState_ :: forall state. Fn2 state (Wrapper SingleNode) (EffectFnAff Unit)

foreign import simulate_ :: EffectFn3 String Foreign (Wrapper SingleNode) Unit

foreign import simulateCustom_ :: EffectFn3 String Foreign (Wrapper SingleNode) Unit

foreign import state_ :: EffectFn1 (Wrapper SingleNode) Foreign

foreign import text_ :: EffectFn1 (Wrapper SingleNode) String

foreign import name_ :: EffectFn1 (Wrapper SingleNode) String

foreign import unmount_ :: EffectFn1 (Wrapper SingleNode) Unit

foreign import update_ :: forall n. EffectFn1 (Wrapper n) Unit
