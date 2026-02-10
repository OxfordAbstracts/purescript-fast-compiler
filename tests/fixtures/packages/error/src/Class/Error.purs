module Error.Class where

class Error error where
    name :: error -> String
    message :: error -> String

foreign import defaultName :: forall error. error -> String

foreign import defaultMessage :: forall error. error -> String
