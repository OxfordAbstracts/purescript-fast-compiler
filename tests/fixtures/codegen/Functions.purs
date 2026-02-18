module Functions where

identity :: forall a. a -> a
identity x = x

constFunc :: forall a b. a -> b -> a
constFunc x _ = x

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

flip :: forall a b c. (a -> b -> c) -> b -> a -> c
flip f b a = f a b

compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
