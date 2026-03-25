module WriterTrans where

import Prelude

newtype WriterT w m a = WriterT (m { value :: a, log :: w })

runWriterT :: forall w m a. WriterT w m a -> m { value :: a, log :: w }
runWriterT (WriterT f) = f

instance functorWriterT :: Functor m => Functor (WriterT w m) where
  map f (WriterT ma) = WriterT (map (\r -> { value: f r.value, log: r.log }) ma)

instance applyWriterT :: (Semigroup w, Monad m) => Apply (WriterT w m) where
  apply (WriterT mf) (WriterT ma) = WriterT (bind mf (\rf ->
    bind ma (\ra -> pure { value: rf.value ra.value, log: rf.log <> ra.log })))

instance applicativeWriterT :: (Monoid w, Monad m) => Applicative (WriterT w m) where
  pure a = WriterT (pure { value: a, log: mempty })

instance bindWriterT :: (Semigroup w, Monad m) => Bind (WriterT w m) where
  bind (WriterT ma) f = WriterT (bind ma (\ra ->
    let WriterT mb = f ra.value in bind mb (\rb ->
      pure { value: rb.value, log: ra.log <> rb.log })))

instance monadWriterT :: (Monoid w, Monad m) => Monad (WriterT w m)
