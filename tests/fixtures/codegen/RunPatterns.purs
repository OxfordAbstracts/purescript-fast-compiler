module RunPatterns where

data Maybe a = Nothing | Just a

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def m = case m of
  Nothing -> def
  Just x -> x

isJust :: forall a. Maybe a -> Boolean
isJust m = case m of
  Nothing -> false
  Just _ -> true
