module Data.ReaderTEtaConversionTransformer where

import Prelude

import Control.Monad.Reader (ReaderT(..))
import Type.Equality (class TypeEquals, to)

class ReaderTFunctionMaker input output | input -> output, output -> input where
  readerT :: input -> output

instance args9 :: TypeEquals r x => ReaderTFunctionMaker
  (x -> a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> m a)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> ReaderT r m a)
  where
  readerT f a1 a2 a3 a4 a5 a6 a7 a8 a9 = ReaderT $ \r -> extract r f a1 a2 a3 a4 a5 a6 a7 a8 a9
else
instance args8 :: TypeEquals r x => ReaderTFunctionMaker
  (x -> a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> m a)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> ReaderT r m a)
  where
  readerT f a1 a2 a3 a4 a5 a6 a7 a8 = ReaderT $ \r -> extract r f a1 a2 a3 a4 a5 a6 a7 a8
else
instance args7 :: TypeEquals r x => ReaderTFunctionMaker
  (x -> a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> m a)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> ReaderT r m a)
  where
  readerT f a1 a2 a3 a4 a5 a6 a7 = ReaderT $ \r -> extract r f a1 a2 a3 a4 a5 a6 a7
else
instance args6 :: TypeEquals r x => ReaderTFunctionMaker
  (x -> a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> m a)
  (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> ReaderT r m a)
  where
  readerT f a1 a2 a3 a4 a5 a6 = ReaderT $ \r -> extract r f a1 a2 a3 a4 a5 a6
else
instance args5 :: TypeEquals r x => ReaderTFunctionMaker
  (x -> a1 -> a2 -> a3 -> a4 -> a5 -> m a)
  (a1 -> a2 -> a3 -> a4 -> a5 -> ReaderT r m a)
  where
  readerT f a1 a2 a3 a4 a5 = ReaderT $ \r -> extract r f a1 a2 a3 a4 a5
else
instance args4 :: TypeEquals r x => ReaderTFunctionMaker
  (x -> a1 -> a2 -> a3 -> a4 -> m a)
  (a1 -> a2 -> a3 -> a4 -> ReaderT r m a)
  where
  readerT f a1 a2 a3 a4 = ReaderT $ \r -> extract r f a1 a2 a3 a4
else
instance args3 :: TypeEquals r x => ReaderTFunctionMaker
  (x -> a1 -> a2 -> a3 -> m a)
  (a1 -> a2 -> a3 -> ReaderT r m a)
  where
  readerT f a1 a2 a3 = ReaderT $ \r -> extract r f a1 a2 a3
else
instance args2 :: TypeEquals r x => ReaderTFunctionMaker (x -> a1 -> a2 -> m a) (a1 -> a2 -> ReaderT r m a) where
  readerT f a1 a2 = ReaderT $ \r -> extract r f a1 a2
else
instance args1 :: TypeEquals r x => ReaderTFunctionMaker (x -> a1 -> m a) (a1 -> ReaderT r m a) where
  readerT f a1 = ReaderT $ \r -> extract r f a1

extract :: forall r x a. TypeEquals r x => r -> (x -> a) -> a
extract r f = f $ to r