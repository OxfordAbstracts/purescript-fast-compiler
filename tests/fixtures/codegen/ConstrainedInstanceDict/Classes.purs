-- | Defines a class hierarchy mimicking MonadTell/Monoid/Monad.
-- | Kept self-contained (no Prelude dependency).
module Classes where

-- Minimal Monoid-like class
class Combine a where
  cempty :: a
  cappend :: a -> a -> a

-- Concrete instance for String (must be in same module as class to avoid orphan)
instance combineString :: Combine String where
  cempty = ""
  cappend a _ = a

-- Minimal Monad-like class (simplified, just one method)
class Wrap (m :: Type -> Type) where
  wpure :: forall a. a -> m a

-- MonadTell-like class: accumulate values
class Accum w (m :: Type -> Type) where
  accum :: w -> m Int
