module RunFunctions where

identity :: forall a. a -> a
identity x = x

constFunc :: forall a b. a -> b -> a
constFunc x _ = x

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x
