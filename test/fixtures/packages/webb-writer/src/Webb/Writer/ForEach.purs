module Webb.Writer.ForEach where

import Prelude

import Control.Monad.State (class MonadState, State, execState)
import Data.Array as A
import Data.Maybe (Maybe(..), isJust)
import Data.TraversableWithIndex (class TraversableWithIndex, forWithIndex)
import Unsafe.Coerce (unsafeCoerce)
import Webb.State.Prelude (class ReferM, mmodify_)


class Length a where
  length :: a -> Int
  
instance Length (Array a) where
  length = A.length

type St = 
  { each :: Maybe Void
  , between :: Maybe Void
  , after :: Maybe Void
  , before :: Maybe Void
  }

newtype ForEach :: forall k1 k2 k3. k1 -> k2 -> k3 -> Type -> Type
newtype ForEach m a b x = FE (State St x)

derive newtype instance Functor (ForEach m a b)
derive newtype instance Apply (ForEach m a b)
derive newtype instance Applicative (ForEach m a b)
derive newtype instance Bind (ForEach m a b)
derive newtype instance Monad (ForEach m a b)
derive newtype instance MonadState St (ForEach m a b)
derive newtype instance ReferM St (ForEach m a b)

forEach :: forall m t a b. 
  Monad m => TraversableWithIndex Int t => Length (t a) => Monoid (t b) =>
  t a -> ForEach m a b Unit -> m (t b)
forEach t (FE prog) = do 
  let fs = execState prog empty 
  results <- forWithIndex t \i a -> do
    let before' = unsafeCoerce $ prep fs.before :: a -> m Unit
        each' = unsafeCoerce $ prep fs.each :: a -> m b
        between' = unsafeCoerce $ prep fs.between :: a -> m Unit
        after' = unsafeCoerce $ prep fs.after :: a -> m Unit
    before' a
    b <- each' a
    when (isBetween t i) do between' a
    after' a
    pure b
    
  if isJust fs.each then do
    pure results
  else do
    pure mempty
  
  where 
  prep :: Maybe Void -> (a -> m Unit)
  prep mf = case mf of
    Nothing -> (\_ -> pure unit)
    Just f -> unsafeCoerce f

  n = Nothing
  empty = { each: n, between: n, after: n, before: n}
  isBetween coll i = let 
    len = length coll
    in if len <= 1 then
      -- 0 or 1 element has no between.
      false
    else if i < len - 1 then
      -- if len is 4, then while we aren't on the last index, we are between.
      true
    else 
      false
      
forEach_ :: forall m t a b. 
  Monad m => TraversableWithIndex Int t => Length (t a) => Monoid (t b) =>
  t a -> ForEach m a b Unit -> m Unit
forEach_ t prog = void $ forEach t prog

before :: forall a b m. Monad m => (a -> m Unit) -> ForEach m a b Unit
before f = do
  mmodify_ $ _ { before = Just $ unsafeCoerce f }

each :: forall a b m. Monad m => (a -> m b) -> ForEach m a b Unit
each f = do
  mmodify_ $ _ { each = Just $ unsafeCoerce f }

inBetween :: forall a b m. Monad m => (a -> m Unit) -> ForEach m a b Unit
inBetween f = do
  mmodify_ $ _ { between = Just $ unsafeCoerce f }

after :: forall a b m. Monad m => (a -> m Unit) -> ForEach m a b Unit
after f = do
  mmodify_ $ _ { after = Just $ unsafeCoerce f }