module TestDeep where

import MyPrelude

-- Uses <$> (myMap from MyFunctor) through MyAlternative constraint,
-- imported via MyPrelude re-export. 2-level superclass chain.
combine :: forall f a b. MyAlternative f => (a -> b) -> f a -> f (a -> b) -> f b
combine f fa fab = f <$> fa
