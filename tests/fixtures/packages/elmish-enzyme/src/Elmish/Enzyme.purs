-- | Bindings for the [Enzyme library](https://enzymejs.github.io/enzyme/) to
-- | use with the [Elmish
-- | library](https://github.com/collegevine/purescript-elmish).
-- |
-- | The API here is presented in monadic style, with the idea that there is
-- | always a "current" DOM element (or, more precisely, current
-- | `Wrapper`, which may refer to zero or more actual DOM elements),
-- | with respect to which all operations run. A test starts with either
-- | `testComponent` or `testElement`, and it's that component (or element) that
-- | becomes the "current" element at the start, for example:
-- |
-- |```purs
-- |-- The main module:
-- |myComponent :: ComponentDef Message State
-- |myComponent = { init, view, update } where ...
-- |
-- |-- The test module:
-- |import Elmish.Enzyme (testComponent, text)
-- |
-- |someTest = it "contains the right text" do
-- |  testComponent myComponent do
-- |    content <- text
-- |    content `shouldContain` "right"
-- |```
-- |
-- | From there, it's possible to "drill down" into a particular element, making
-- | it "current" temporarily, via `withSelector` or `withElement` (similar to
-- | Capybara's `within`), for example:
-- |
-- |```purs
-- |import Elmish.Enzyme (testComponent, text, withSelector)
-- |
-- |someTest = it "has two buttons with the right text" do
-- |  testComponent myComponent do
-- |    withSelector "button.first-button" do
-- |      content <- text
-- |      content `shouldEqual` "I'm the first button!"
-- |
-- |    withSelector "button.second-button" do
-- |      content <- text
-- |      content `shouldEqual` "I'm the second button!"
-- |```
-- |
-- | Alternatively, operations that return a `Wrapper` may be combined
-- | in a chain using the `>>` operator (which is just a convenient facade for
-- | `withElement` under the hood):
-- |
-- |```purs
-- |import Elmish.Enzyme (testComponent, text, find, findAll, at, (>>))
-- |
-- |someTest = it "has two buttons with the right text" do
-- |  testComponent myComponent do
-- |    -- A short chain, just two functions:
-- |    b1 <- find "button.first-button" >> text
-- |    b1 `shouldEqual` "I'm the first button!"
-- |
-- |    -- A longer chain: `findAll`, then `at`, then `text`
-- |    b2 <- findAll "button" >> at 1 >> text
-- |    b2 `shouldEqual` "I'm the second button!"
-- |
-- |    -- An even longer chain:
-- |    b3 <- findAll ".card" >> at 3 >> findAll "button" >> at 1 >> text
-- |    b3 `shouldEqual` "I'm second button in 4th card!"
-- |```
-- |
-- | The end result is an API that somewhat resembles how Emzyme would be used
-- | from JavaScript, as well as other similar testing libraries, sych as
-- | Capybara.
module Elmish.Enzyme
  ( EnzymeM
  , testComponent, testElement
  , at
  , childAt
  , children
  , clickOn
  , count
  , debug
  , exists
  , find
  , findAll
  , forEach
  , is
  , length
  , mapEach
  , name
  , parent
  , prop
  , simulate, simulate', simulateCustom'
  , spy
  , state
  , text
  , toArray
  , trace
  , unsafeSetState
  , update
  , waitUntil, waitUntil'
  , waitWhile, waitWhile'
  , withElement, withElementM
  , withSelector
  , (>>)
  , module ForeignExports
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT, withReaderT)
import Data.Traversable (traverse)
import Debug (class DebugWarning)
import Effect.Aff (Aff, Milliseconds(..), delay, error, throwError)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class.Console (log)
import Elmish (ReactElement)
import Elmish.Component (ComponentDef)
import Elmish.Enzyme.Foreign (ManyNodes, NodeMultiplicity, SingleNode, Wrapper)
import Elmish.Enzyme.Foreign (Wrapper, SingleNode, ManyNodes, configure) as ForeignExports
import Elmish.Enzyme.Foreign as E
import Foreign (Foreign)
import Unsafe.Coerce (unsafeCoerce)

-- | Monad for running Enzyme tests. Keeps a reference to the "current" DOM
-- | element(s) and tracks the current element's multiplicity (whether it's a
-- | single node or multiple) at type level (the `context` parameter), allowing
-- | to check validity of certain functions at compile-time (e.g. `text` only
-- | works on a single element).
type EnzymeM (context :: NodeMultiplicity) = ReaderT (Wrapper context) Aff

-- | Mounts the given component and runs the given action with the mounted
-- | component as current context.
-- |
-- | ```purescript
-- | it "displays content" do
-- |   testComponent (MyComponent.def props) do
-- |     exists ".t--my-content" >>= shouldEqual true
-- | ```
testComponent :: forall m msg state. MonadAff m => ComponentDef msg state -> EnzymeM SingleNode Unit -> m Unit
testComponent component test = liftAff do
  wrapper <- E.mountComponent component
  runReaderT test wrapper
  E.unmount wrapper

-- | Mounts the given element and runs the given action with the mounted element
-- | as current context.
-- |
-- | ```purescript
-- | pending' "displays content"
-- |   testElement (MyElement.render props) do
-- |     exists ".t--my-content" >>= shouldEqual true
-- | ```
testElement :: forall m. MonadAff m => ReactElement -> EnzymeM SingleNode Unit -> m Unit
testElement element test = liftAff do
  wrapper <- E.mount element
  runReaderT test wrapper
  E.unmount wrapper

-- | The current context can contain multiple DOM elements. This function
-- | returns the element at the given index (zero-based). See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/at.html for more
-- | info.
-- |
-- |```purs
-- |findAll "button" >> at 3 >> text >>= shouldEqual "Fourth button"
-- |```
at :: Int -> EnzymeM ManyNodes (Wrapper SingleNode)
at index = E.at index =<< ask

-- | Returns the string representing the DOM tree of the current element(s). See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/debug.html for more
-- | info.
debug :: forall n. DebugWarning => EnzymeM n String
debug = E.debug =<< ask

-- | Logs a string representing the DOM tree of the current element(s).
trace :: forall n. DebugWarning => EnzymeM n Unit
trace = log =<< debug

-- | Logs a string representing the DOM tree of the current element(s) and
-- | returns the original `Wrapper`, so that it can be used in a `withElementM`
-- | chain, like so:
-- |
-- | ```purs
-- | spy >> find "foo" >> spy >> childAt 0 >> spy >> text >>= shouldEqual "Foo"
-- | ```
spy :: forall n. DebugWarning => EnzymeM n (Wrapper n)
spy = ask <* trace

-- | Returns a `Boolean` indicating whether a given selector exists within the
-- | current element.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/exists.html
-- | for more info.
exists :: forall n. String -> EnzymeM n Boolean
exists selector = E.exists selector =<< ask

-- | Finds all elements matching the given selector within the current
-- | context.
-- |
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/find.html for
-- | more info.
findAll :: forall n. String -> EnzymeM n (Wrapper ManyNodes)
findAll selector = E.find selector =<< ask

-- | Finds a single element matching the given selector within the current
-- | context. If zero or multiple elements match the selector, crashes with a
-- | descriptive error message.
-- |
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/find.html for
-- | more info.
find :: forall n. String -> EnzymeM n (Wrapper SingleNode)
find selector = do
  els <- findAll selector
  when (E.length els /= 1) $
    liftAff $ throwError $ error $
      "Expected a single element matching '" <> selector <> "', but found " <> show (E.length els)
  pure $ unsafeCoerce els

-- | Returns parent of the current element. When the current context contains
-- | multiple elements, the result will contain exactly as many parents, even if
-- | some of the elements have the same parent. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/parent.html for more
-- | info.
parent :: forall n. EnzymeM n (Wrapper n)
parent = E.parent =<< ask

-- | Returns the child nodes of the current `Wrapper`. When the current context
-- | contains multiple elements, the result will contain the children of each
-- | element. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/children.html for
-- | more info.
children :: forall n. EnzymeM n (Wrapper ManyNodes)
children = E.children =<< ask

-- | Returns the child node at index `idx` of the current `Wrapper`.`childAt n`
-- | is equivalent to `children >> at n` See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/childAt.html ffor
-- | more info.
childAt :: forall n. Int -> EnzymeM n (Wrapper SingleNode)
childAt n = E.childAt n =<< ask

-- | Returns a `Boolean` indicating whether the current element matches
-- | the given selector.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/is.html
-- | for more info.
is :: String -> EnzymeM SingleNode Boolean
is selector = E.is selector =<< ask

-- | Returns the value of the current element’s prop with a certain key.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/prop.html
-- | for more info.
prop :: forall a. String -> EnzymeM SingleNode a
prop key = E.prop key =<< ask

-- | Sets the state of the current element. Note that this is
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/setState.html
-- | for more info.
-- |
-- | NOTE: this is a type-unsafe operation. There is no check to make sure the
-- | state being set here has the type of the actual state the component in
-- | question is using.
unsafeSetState :: forall state. state -> EnzymeM SingleNode Unit
unsafeSetState newState =
  E.unsafeSetState newState =<< ask

-- | A convenience function for calling `simulate'` without an `event` arg.
simulate :: String -> EnzymeM SingleNode Unit
simulate eventType =
  E.simulate eventType =<< ask

-- | Simulates a certain event type on the current element. The event argument
-- | is a record that gets merged with a simulated React synthetic event before
-- | being passed to the component’s event handler. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/simulate.html for
-- | more info.

-- | NOTE: This doesn’t actually emit an event, but just triggers the event
-- | handler on the wrapper.
-- |
-- | NOTE 2: This function only works for native HTML elements. For emitting
-- | events on custom React components, use `simulateCustom`.
simulate' :: forall r. String -> Record r -> EnzymeM SingleNode Unit
simulate' eventType event =
  E.simulate' eventType event =<< ask

-- | Simulates an event on a custom React component (i.e. not an HTML element).
-- | For reasons to complicated to discuss here, the regular `simulate` doesn't
-- | work on custom components, so we provide this workaround.
-- |
-- | NOTE: the second parameter is passed to the event handler without any
-- | checks whatsoever. This is, of course, not type-safe, but it is in line
-- | with what the event handler should expect anyway: after all, the underlying
-- | JavaScript component may pass anything at all as event argument.
simulateCustom' :: forall a. String -> a -> EnzymeM SingleNode Unit
simulateCustom' eventType event =
  E.simulateCustom' eventType event =<< ask

-- | A convienience shorthand for clicking an element known by CSS selector
clickOn :: forall n. String -> EnzymeM n Unit
clickOn selector = find selector >> simulate "click"

-- | Returns the state of the current element. See
-- | https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/state.html for more
-- | info.
state :: EnzymeM SingleNode Foreign
state = E.state =<< ask

-- | Returns the text within the current element.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/text.html
-- | for more info.
text :: EnzymeM SingleNode String
text = E.text =<< ask

-- | Returns tag name of the current element.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/name.html
-- | for more info.
name :: EnzymeM SingleNode String
name = E.name =<< ask

-- | Returns the number of times a given selector appears.
count :: forall n. String -> EnzymeM n Int
count selector = E.count selector =<< ask

-- | Updates the current element to reflect the latest state. Call this function
-- | whenever you think there could be an async change of state that caused a
-- | re-render. For some reason, Enzyme won't pick up the changes automatically.
-- | See https://enzymejs.github.io/enzyme/docs/api/ReactWrapper/update.html for
-- | more info.
-- |
-- | NOTE: this only works on the "root" element, which means it cannot be
-- | called inside `withSelector` or `withElement`.
update :: forall n. EnzymeM n Unit
update = E.update =<< ask

-- | Takes a `Wrapper` and runs an `EnzymeM` computation with the given
-- | wrapper as the new implicit wrapper. This can be thought of as analogous to
-- | Capybara’s `within`.
-- |
-- | ```purescript
-- | button <- find "button.my-button"
-- | withElement button do
-- |   simulate "click"
-- |   prop "disabled" >>= shouldEqual true
-- | ```
withElement :: forall a nOuter nInner. Wrapper nInner -> EnzymeM nInner a -> EnzymeM nOuter a
withElement wrapper =
  withReaderT $ const wrapper

-- | A version of `withElement` that takes the `Wrapper` wrapped in
-- | `EnzymeM` rather than "naked". Aliased as the `>>` operator, this allows
-- | for handy chaining of operations that return a `Wrapper`, for
-- | example:
-- |
-- | ```purescript
-- | findAll ".foo" >> at 1 >> find ".bar" >> simulate "click"
-- | ```
withElementM :: forall a nOuter nInner. EnzymeM nOuter (Wrapper nInner) -> EnzymeM nInner a -> EnzymeM nOuter a
withElementM el f = el >>= \e -> withElement e f

infixl 1 withElementM as >>

-- | Basically, a DSL-friendly equivalent of `map`: for each element in the
-- | current `Wrapper` performs the given action and returns all results
-- | of that action as an array.
-- |
-- | Example:
-- |
-- |     allNames <- findAll ".t--foo" >> mapEach text
-- |     allValues <- findAll ".t--foo" >> mapEach (prop "value")
-- |
mapEach :: forall a. EnzymeM SingleNode a -> EnzymeM ManyNodes (Array a)
mapEach f = toArray >>= traverse \e -> withElement e f

-- | Returns all elements contained in the current `Wrapper` as an array.
toArray :: EnzymeM ManyNodes (Array (Wrapper SingleNode))
toArray = E.toArray =<< ask

-- | Basically, a DSL-friendly equivalent of `for_`: for each element in the
-- | current `Wrapper` performs the given effect.
-- |
-- | Example:
-- |
-- |     findAll "button" >> forEach (simulate "click")
-- |
-- |     findAll ".t--foo" >> forEach do
-- |       find "input[type=text]" >> simulate' "change" { target: { value: "new text" } }
-- |       find "input[type=checkbox]" >> simulate "change"
-- |       find ".t--bar" >> text >>= shouldEqual "qux"
-- |
forEach :: EnzymeM SingleNode Unit -> EnzymeM ManyNodes Unit
forEach f = E.forEach (\e -> withElement e f) =<< ask

-- | Returns number of elements in the current context
length :: EnzymeM ManyNodes Int
length = E.length <$> ask

-- | A convenience function which finds an element for the given selector and
-- | passes it to `withElement`.
-- |
-- | ```purescript
-- | withSelector ".t--my-button" do
-- |   simulate "click"
-- |   prop "disabled" >>= shouldEqual true
-- | ```
withSelector :: forall a n. String -> EnzymeM SingleNode a -> EnzymeM n a
withSelector selector m = do
  wrapper <- find selector
  withElement wrapper m

-- | Performs active wait while the given condition is true. Times out with a
-- | crash after a second.
waitWhile :: forall n. EnzymeM n Boolean -> EnzymeM n Unit
waitWhile = waitWhile' (Milliseconds 1000.0)

-- | Performs active wait while the given condition is false. Times out with a
-- | crash after a second.
waitUntil :: forall n. EnzymeM n Boolean -> EnzymeM n Unit
waitUntil = waitUntil' (Milliseconds 1000.0)

-- | Performs active wait while the given condition is true. Times out with a
-- | crash after given time period.
waitWhile' :: forall n. Milliseconds -> EnzymeM n Boolean -> EnzymeM n Unit
waitWhile' timeout f = waitUntil' timeout $ not <$> f

-- | Performs active wait while the given condition is true. Times out with a
-- | crash after given time period.
waitUntil' :: forall n. Milliseconds -> EnzymeM n Boolean -> EnzymeM n Unit
waitUntil' (Milliseconds timeout) f = go timeout
  where
    go remaining = do
      when (remaining <= 0.0) $
        liftAff $ throwError $ error "Timeout expired"
      liftAff $ delay $ Milliseconds 1.0
      update
      unlessM f $ go $ remaining - 1.0
