module Jelly.Router where

import Prelude

import Control.Monad.Reader (ReaderT, asks, lift, runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Foreign (unsafeToForeign)
import Jelly.Component (Component)
import Jelly.Element (a)
import Jelly.Hooks (class MonadHooks, useEvent, useStateEq)
import Jelly.Prop (Prop, on, (:=))
import Jelly.Signal (Signal, writeChannel)
import Web.Event.Event (preventDefault)
import Web.HTML (window)
import Web.HTML.Event.EventTypes (click)
import Web.HTML.Event.PopStateEvent.EventTypes (popstate)
import Web.HTML.History (DocumentTitle(..), URL(..), pushState, replaceState)
import Web.HTML.Location (hash, pathname, search)
import Web.HTML.Window (history, location)
import Web.HTML.Window as Window

-- | `Router m` represents you can use routing in Monad `m`.
class MonadEffect m <= Router m where
  -- | Push a new Route to the browser history.
  usePushRoute :: String -> m Unit
  -- | Replace the current Route in the browser history.
  useReplaceRoute :: String -> m Unit
  -- | Get the current Route.
  useCurrentRoute :: m (Signal String)

-- | RouterR is a global values for RouterT.
type RouterR =
  { pushState :: String -> Effect Unit
  , replaceState :: String -> Effect Unit
  , currentRoute :: Signal String
  }

-- | RouterT is a Monad for Router.
newtype RouterT :: forall k. (k -> Type) -> k -> Type
newtype RouterT m a = RouterT (ReaderT RouterR m a)

derive newtype instance Monad m => Functor (RouterT m)
derive newtype instance Monad m => Apply (RouterT m)
derive newtype instance Monad m => Applicative (RouterT m)
derive newtype instance Monad m => Bind (RouterT m)
derive newtype instance Monad m => Monad (RouterT m)
derive newtype instance MonadEffect m => MonadEffect (RouterT m)
derive newtype instance MonadRec m => MonadRec (RouterT m)
derive newtype instance MonadHooks m => MonadHooks (RouterT m)
instance MonadEffect m => Router (RouterT m) where
  usePushRoute route = RouterT $ asks _.pushState >>= \push -> liftEffect $ push route
  useReplaceRoute route = RouterT $ asks _.replaceState >>= \replace -> liftEffect $ replace route
  useCurrentRoute = RouterT $ asks _.currentRoute

instance Router m => Router (ReaderT r m) where
  usePushRoute = lift <<< usePushRoute
  useReplaceRoute = lift <<< useReplaceRoute
  useCurrentRoute = lift useCurrentRoute

-- | Run a RouterT.
runRouterT :: forall m a. MonadHooks m => RouterT m a -> m a
runRouterT (RouterT rdr) = do
  routerR <- initRouter
  runReaderT rdr routerR

-- | Run a RouterT outside of the browser.
-- | This is useful for SSG.　
runMockRouterT :: forall m a. MonadHooks m => RouterT m a -> String -> m a
runMockRouterT (RouterT rdr) initRoute = do
  currentRoute /\ crChn <- useStateEq initRoute
  runReaderT rdr
    { pushState: writeChannel crChn
    , replaceState: writeChannel crChn
    , currentRoute
    }

initRouter :: forall m. MonadHooks m => m RouterR
initRouter = do
  w <- liftEffect window
  initRoute <- liftEffect do
    l <- location w
    pn <- pathname l
    sr <- search l
    hs <- hash l
    pure $ pn <> sr <> hs

  currentRoute /\ crChn <- useStateEq initRoute
  let
    handleRoute handleFn route = do
      handleFn (unsafeToForeign {}) (DocumentTitle "")
        (URL $ route) =<< history w
      writeChannel crChn route

    routerR =
      { pushState: handleRoute pushState
      , replaceState: handleRoute replaceState
      , currentRoute
      }

  useEvent (Window.toEventTarget w) popstate \_ -> do
    route <- liftEffect do
      l <- location w
      pn <- pathname l
      sr <- search l
      hs <- hash l
      pure $ pn <> sr <> hs
    writeChannel crChn route

  pure routerR

-- | Router link component.
-- | This is the `a` element, but when clicked, it does preventDefault and does SPA routing.
routerLink :: forall m. MonadEffect m => Router m => String -> Array (Prop m) -> Component m -> Component m
routerLink route props component = do
  let
    handleClick e = do
      liftEffect $ preventDefault e
      usePushRoute route

  a ([ on click handleClick, "href" := route ] <> props) component

-- | Same as `routerLink`, but without Props.
routerLink' :: forall m. MonadEffect m => Router m => String -> Component m -> Component m
routerLink' route component = routerLink route [] component
