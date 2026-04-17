module Test.Multi.CtorB where

-- `Maybe(..)` brings both constructors into scope so they can
-- be used in patterns + expressions here.
import Test.Multi.CtorA (Maybe(..))

first :: forall a. Maybe a -> Maybe a
first Nothing = Nothing
first (Just x) = Just x
