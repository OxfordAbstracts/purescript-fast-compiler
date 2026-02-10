module Error where

import Error.Class (class Error, defaultMessage, defaultName)

foreign import data Error :: Type

instance errorError :: Error Error where
    name = defaultName
    message = defaultMessage
