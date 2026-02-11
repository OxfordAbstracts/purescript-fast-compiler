module Graphics.CanvasAction.Types where

import Control.Monad.Reader.Trans (ReaderT(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect, class MonadEffect)
import Graphics.Canvas (Context2D)

-- | The `CanvasAction` monad is a monad transformer stack, more specifically
-- | the `ReaderT` monad transformer applied to the `Effect` monad, reading a
-- | value of type `Context2D`.
type CanvasAction = ReaderT Context2D Effect

-- | Run a `CanvasAction` in a `MonadEffect`, on the provided `Context2D`.
runAction ∷ ∀ m a. MonadEffect m ⇒ Context2D → CanvasAction a → m a
runAction ctx (ReaderT action) = liftEffect (action ctx)

-- | The `CanvasAff` monad is a monad transformer stack, more specifically
-- | the `ReaderT` monad transformer applied to the `Aff` monad, reading a
-- | value of type `Context2D`.
type CanvasAff = ReaderT Context2D Aff

-- | Run a `CanvasAff` in a `MonadAff`, on the provided `Context2D`.
runCanvasAff ∷ ∀ m a. MonadAff m ⇒ Context2D → CanvasAff a → m a
runCanvasAff ctx (ReaderT action) = liftAff (action ctx)
