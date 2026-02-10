module WebExtension.Polyfill where

import Prelude
import Control.Promise (Promise, toAffE)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Semigroup.Foldable (intercalateMap)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class.Console as Console
import Effect.Uncurried (EffectFn1, EffectFn2, mkEffectFn1, runEffectFn1, runEffectFn2)
import Foreign (Foreign, renderForeignError)
import Foreign.Object (Object)
import Foreign.Object as Object
import Prim.Row (class Union)
import Yoga.JSON (class ReadForeign, class WriteForeign, read)
import Yoga.JSON as JSON
import WebExtension.Polyfill.Types (StorageKey(..))

foreign import browserImpl ∷ Type

-- Unusal API. The keys could also be an array in which case there'd be an object
-- with keys for the array of strings passed in originally values. Maybe this is
-- for efficiency reasons when using the "sync" API which is apparently kind of
-- throttled. Until then, we store keys and values.
foreign import data LocalStorage ∷ Type

foreign import loadFromLocalStorageImpl ∷ String -> Effect (Promise (Object Foreign))

foreign import saveInLocalStorageImpl ∷ Object Foreign -> Effect (Promise Unit)

foreign import removeFromLocalStorageImpl ∷ String -> Effect (Promise Unit)

loadFromLocalStorage ∷ ∀ a. ReadForeign a => StorageKey -> Aff (Maybe a)
loadFromLocalStorage (StorageKey key) = do
  Console.info $ "Loading from Local Storage " <> key
  result <- toAffE $ loadFromLocalStorageImpl key
  pure case Object.lookup key result of
    Nothing -> Nothing
    Just raw -> JSON.read_ raw

saveInLocalStorage ∷ ∀ a. WriteForeign a => StorageKey -> a -> Aff Unit
saveInLocalStorage (StorageKey key) value = do
  Console.info $ "Saving in Local Storage " <> key <> " : " <> JSON.writeJSON value
  saveInLocalStorageImpl (Object.singleton key $ JSON.write value) # toAffE

removeFromLocalStorage ∷ StorageKey -> Aff Unit
removeFromLocalStorage (StorageKey key) = do
  Console.info $ "Removing from Local Storage " <> key
  removeFromLocalStorageImpl key # toAffE

foreign import data Port ∷ Type

foreign import sendMessageViaPortImpl ∷ EffectFn2 Foreign Port Unit

sendMessageViaPort ∷ ∀ msg. WriteForeign msg => msg -> Port -> Effect Unit
sendMessageViaPort m = runEffectFn2 sendMessageViaPortImpl (JSON.write m)

foreign import addOnPortMessageListenerImpl ∷ EffectFn2 (EffectFn1 Foreign Unit) Port Unit

addOnPortMessageListener ∷ (Foreign -> Effect Unit) -> Port -> Effect Unit
addOnPortMessageListener listener = runEffectFn2 addOnPortMessageListenerImpl (mkEffectFn1 listener)

foreign import onContentScriptConnectedImpl ∷ (Port -> Effect Unit) -> Effect Unit

onContentScriptConnected ∷ (Port -> Effect Unit) -> Effect Unit
onContentScriptConnected = onContentScriptConnectedImpl

type ConnectOptions =
  (name ∷ String)

foreign import connectToBackgroundScriptImpl ∷ ∀ opts. EffectFn1 (Record opts) Port

connectToBackgroundScript ∷ ∀ opts missing. Union opts missing ConnectOptions => Record opts -> Effect Port
connectToBackgroundScript = runEffectFn1 connectToBackgroundScriptImpl

foreign import openNewWindowImpl ∷ ∀ opts. Record opts -> Effect Unit

openNewWindow ∷ ∀ opts. Record opts -> Effect Unit
openNewWindow = openNewWindowImpl

foreign import reload ∷ Effect Unit

foreign import data BrowserHistory ∷ Type

foreign import history ∷ Effect BrowserHistory

foreign import addOnVisitedListenerImpl ∷ (EffectFn1 Foreign Unit) -> BrowserHistory -> Effect Unit

addOnVisitedListener
  ∷ (HistoryItem -> Effect Unit)
  -> BrowserHistory
  -> Effect Unit
addOnVisitedListener callback = addOnVisitedListenerImpl (mkEffectFn1 rawCallback)
  where
  rawCallback f = do
    let parsed = read f
    case parsed of
      Left err ->
        Console.error
          $ "Could not parse history item "
              <> intercalateMap "\n" renderForeignError err
      Right ok -> callback ok

type HistoryItem =
  { id ∷ String
  , url ∷ Maybe String
  , title ∷ Maybe String
  , lastVisitTime ∷ Maybe Number -- really an instant
  , visitCount ∷ Maybe Int
  }
