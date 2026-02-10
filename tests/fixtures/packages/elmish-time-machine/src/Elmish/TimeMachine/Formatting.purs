module Elmish.TimeMachine.Formatting
  ( JsPrim
  , Value(..)
  , formatMessage
  , formatValue
  , toValue
  )
  where

import Prelude

import Data.Array as Array
import Data.Function.Uncurried (Fn1, runFn1)
import Data.Monoid (guard)
import Elmish.TimeMachine.Types.Message (Message(..))
import Unsafe.Coerce (unsafeCoerce)

-- | A semi-opaque type representing any value to be formatted
data Value
  = VCustom String (Array Value)
  | VObject (Array { key :: Value, value :: Value })
  | VArray (Array Value)
  | VPrim JsPrim

-- | An opaque type representing a primitive value
foreign import data JsPrim :: Type

-- | Formats a message, using either a full representation or a just the
-- | constructor
formatMessage :: ∀ msg. Boolean -> Message msg -> String
formatMessage full = case _ of
  Init -> "Initial State"
  Message msg
    | full -> format msg
    | otherwise -> tagFromJsValue $ unsafeCoerce msg

-- | Converts any value to a `Value`
toValue :: ∀ a. a -> Value
toValue = unsafeCoerce >>> fromJsValue' >>> fromIntermediate
  where
    fromJsValue' = runFn1 fromJsValue_
    fromIntermediate { tag, value }
      | tag == "VObject" = VObject $ fromKeyValue <$> unsafeCoerce value
      | tag == "VArray" = VArray $ fromIntermediate <$> unsafeCoerce value
      | tag == "VPrim" = VPrim $ unsafeCoerce value
      | otherwise = VCustom tag $ fromIntermediate <$> unsafeCoerce value
    fromKeyValue { key, value } = { key: fromIntermediate key, value: fromIntermediate value }

-- | Formats a `Value` as a string
formatValue :: Value -> String
formatValue v = formatValue' { parens: false } v

formatValue' :: { parens :: Boolean } -> Value -> String
formatValue' { parens } = case _ of
  VCustom tag args -> formatCustom { parens } tag args
  VObject obj -> formatObject obj
  VArray arr -> formatArray arr
  VPrim prim -> formatPrim prim

-- | Formats any value as a string
format :: ∀ a. a -> String
format = toValue >>> formatValue

formatCustom :: { parens :: Boolean } -> String -> Array Value -> String
formatCustom { parens } tag args = Array.fold
  [ guard addParens "("
  , tag
  , guard (not Array.null args) " "
  , args <#> formatValue' { parens: true } # Array.intercalate " "
  , guard addParens ")"
  ]
  where
    addParens = parens && not Array.null args

formatObject :: Array { key :: Value, value :: Value } -> String
formatObject obj = Array.fold
  [ "{ "
  , obj <#> (\{ key, value } -> formatValue' { parens: true } key <> ": " <> formatValue value) # Array.intercalate ", "
  , " }"
  ]

formatArray :: Array Value -> String
formatArray arr = Array.fold
  [ "["
  , arr <#> formatValue # Array.intercalate ", "
  , "]"
  ]

formatPrim :: JsPrim -> String
formatPrim = runFn1 formatPrim_

tagFromJsValue :: JsValue -> String
tagFromJsValue = runFn1 fromJsValue_ >>> _.tag

foreign import data JsValue :: Type

foreign import data Opaque :: Type

foreign import formatPrim_ :: Fn1 JsPrim String

foreign import fromJsValue_ :: Fn1 JsValue { tag :: String, value :: Opaque }
