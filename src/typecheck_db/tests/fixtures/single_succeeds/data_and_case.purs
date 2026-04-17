module Test.DataAndCase where

-- User-defined ADT with a nullary and a single-field constructor.
data Maybe a = Nothing | Just a

-- Pattern matching on the ADT — exhaustive across both
-- constructors so the exhaustiveness check stays quiet.
mapMaybe :: forall a b. (a -> b) -> Maybe a -> Maybe b
mapMaybe f m = case m of
  Nothing -> Nothing
  Just x -> Just (f x)

-- Multi-equation function: each clause handles one constructor.
-- MDd merges these into a single case-bodied decl.
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe d Nothing = d
fromMaybe _ (Just x) = x

-- Nested constructor pattern — single-field recursion into `Just`.
flatten :: forall a. Maybe (Maybe a) -> Maybe a
flatten Nothing = Nothing
flatten (Just Nothing) = Nothing
flatten (Just (Just x)) = Just x
