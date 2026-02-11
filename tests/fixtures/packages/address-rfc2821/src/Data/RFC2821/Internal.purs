module Data.RFC2821.Internal
  (
      Address
    , makeAddress

    , host
    , original
    , originalHost
    , user

    , address
    , toString
  )
where

import Data.Either (Either(..))
import Effect.Exception (Error)
import FFI.Simple ((..), (...))
import Prelude

  
foreign import data Address :: Type

foreign import makeAddressImpl :: forall a b. (Error -> Either Error a)
                               -> (Address -> Either b Address)
                               -> String
                               -> Either Error Address

-- | Attempt to parse given string as an email adddress
makeAddress :: String -> Either Error Address
makeAddress email = makeAddressImpl Left Right email


-- | Return the (parsed) host part `Address`
host :: Address -> String
host a = a .. "host"

-- | Return the original string from `Address`
original :: Address -> String
original a = a .. "original"

-- | Return the original host from `Address`
originalHost :: Address -> String
originalHost a = a .. "original_host"

-- | Return the (parsed) user parf of `Address`
user :: Address -> String
user a = a .. "user"

-- | Format `Address` as a string
address :: Address -> String
address a = a ... "address" $ []

-- | Format `Address` as an envelope
toString :: Address -> String
toString a = a ... "toString" $ []
