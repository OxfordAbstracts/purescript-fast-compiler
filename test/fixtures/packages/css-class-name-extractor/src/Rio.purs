module CssClassNameExtractor.RIO where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Reader.Class (class MonadAsk)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)

type Env = {}

newtype RIO a = RIO (ReaderT Env Aff a)

derive newtype instance functorRIO :: Functor RIO
derive newtype instance applyRIO :: Apply RIO
derive newtype instance applicativeRIO :: Applicative RIO
derive newtype instance bindRIO :: Bind RIO
derive newtype instance monadRIO :: Monad RIO
derive newtype instance monadEffectRIO :: MonadEffect RIO
derive newtype instance monadAffRIO :: MonadAff RIO

instance MonadAsk Env RIO where
  ask = RIO ask

runRIO :: forall a. Env -> RIO a -> Aff a
runRIO env (RIO m) = runReaderT m env
