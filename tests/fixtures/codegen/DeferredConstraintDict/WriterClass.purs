module WriterClass where

import Prelude
import WriterTrans (WriterT(..))

class MonadTell w m where
  tell :: w -> m Unit

instance monadTellWriterT :: (Monoid w, Monad m) => MonadTell w (WriterT w m) where
  tell w = WriterT (pure { value: unit, log: w })
