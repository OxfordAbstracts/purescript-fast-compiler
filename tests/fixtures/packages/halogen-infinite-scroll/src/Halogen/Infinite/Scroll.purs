module Halogen.Infinite.Scroll (class FeedOrder, feedOrder, class Feed, ScrollFeed(..), element, onElement, feedAbove, feedBelow, feedInsert, feedDelete, FeedParams,defaultFeedParams,component ) where

import Prelude hiding (top, bottom)

import CSS (height, marginRight, opacity, paddingRight, pct, position, relative, top, width, zIndex)
import CSS.Overflow (overflow, overflowY, scroll, hidden, overflowAuto)
import CSS.Size (px)
import Control.Monad.Free (Free, liftF, runFreeM)
import Control.Monad.Rec.Class (tailRecM, Step(..))
import Control.Monad.Resource (Resource, runResource)
import Control.Monad.State (State, execState, modify_)
import Data.Array (cons, fold, head, last, null)
import Data.Array as A
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Options ((:=))
import Data.Ord (abs)
import Data.Traversable (sum, traverse, traverse_)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.Aff (delay, Milliseconds(..))
import Effect.Aff.AVar (new, put, tryTake)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.CSS (style)
import Halogen.HTML.Properties as HP
import Halogen.Subscription as HS
import Pipes ((>->))
import Pipes.Core (Producer)
import Pipes.Prelude as Pipes
import Prelude as Prelude
import Type.Proxy (Proxy(..))
import Web.DOM.Element (Element, scrollTop, setScrollTop)
import Web.Intersection.Observer (newIntersectionObserver)
import Web.Intersection.Observer as WIO
import Web.Intersection.Observer.Entry (IntersectionObserverEntry)
import Web.Intersection.Observer.Options (root)
import Web.Resize.Observer (newResizeObserver)
import Web.Resize.Observer as WRO
import Web.Resize.Observer.Entry (ResizeObserverEntry)

class (Ord e) <= FeedOrder e where
  feedOrder :: e -> e -> Ordering

class (FeedOrder e, MonadAff m) <= Feed e m where
  element :: forall q o . H.Component q e o m
  onElement :: e -> m Unit
  feedAbove :: e -> m (Producer e Resource Unit)
  feedBelow :: e -> m (Producer e Resource Unit)
  feedInsert :: m (Maybe (HS.Emitter e))
  feedDelete :: m (Maybe (HS.Emitter e))

type FeedParams e =
  { initialElement :: e
  , pageSize :: Int
  , hiddenPages :: Int
  , preloadedPages :: Int
  , enableTop :: Boolean
  , preloadMillis :: Number
  }

defaultFeedParams :: forall e . e -> FeedParams e
defaultFeedParams e = 
  { initialElement: e
  , pageSize: 10
  , hiddenPages: 3
  , preloadedPages: 3 
  , enableTop: false 
  , preloadMillis: 333.3
  }

data ScrollFeed = ScrollFeed (Number -> Effect Unit)

component :: forall e q m .
             Ord e
          => Feed e m
          => H.Component q (FeedParams e) ScrollFeed m
component =
  H.mkComponent
    { initialState: \feedParams ->
                          { feedParams
                          , pages: Map.empty 
                          , preloaded: Map.empty
                          , lock: Nothing
                          , update: { topLoad: Nothing, bottomLoad: Nothing, scroll: Nothing }
                          }
    , render: renderFeed
    , eval: H.mkEval $ H.defaultEval { handleAction = handleFeedAction
                                     , initialize = Just InitializeFeed
                                     }
    }

data Pos = Below Int | Inside Int | Above Int

instance Monoid Pos where
  mempty = Below Prelude.top

instance Semigroup Pos where
  append (Inside a) _ = Inside a
  append _ (Inside a) = Inside a
  append (Below a) (Below b) = Below (min a b)
  append (Above a) (Above b) = Above (max a b)
  append (Below a) _ = Inside a
  append (Above a) _ = Inside a

findBucket :: forall e . FeedOrder e => e -> Map Int (Page e) -> Int
findBucket e m =
  case fold $ List.toUnfoldable $ Map.values (bounds <$> m) of
    Below a -> a
    Above a -> a
    Inside a -> a
  where
    bounds { id, elements } = 
      case (head elements /\ last elements) of
        (Just h /\ Just l)->
          case (e `feedOrder` h /\ e `feedOrder` l) of
              (LT /\ _) -> Below id
              (_ /\ GT) -> Above id
              _ -> Inside id
        _ -> Above id

type FeedState e =
  { feedParams :: FeedParams e
  , pages :: Map Int (Page e)
  , preloaded :: Map Int (Page e)
  , lock :: Maybe (AVar Unit)
  , update :: {
        topLoad :: Maybe { key :: Int, value :: Page e }
      , bottomLoad :: Maybe { key :: Int, value :: Page e }
      , scroll :: Maybe Number
      }
  }

data FeedAction e =
    InitializeFeed
  | PageOutput PageOutput
  | FeedInsertElement e

type FeedSlots e = ( page :: H.Slot (PageInsert e) PageOutput Int )
_page = Proxy :: Proxy "page"


handleFeedAction :: forall e m .
                    Feed e m
                 => FeedAction e -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) ScrollFeed m Unit
handleFeedAction InitializeFeed = do
  H.getRef (H.RefLabel "feed") >>= traverse_ initializeFeed
  e <- H.lift feedInsert
  traverse_ (\x -> void $ H.subscribe (FeedInsertElement <$> x)) e
  where
    initializeFeed feed = do
      H.raise $ ScrollFeed $ \n -> do
        t <- scrollTop feed
        setScrollTop (t + n) feed
      zerothPage <- loadInitialPage feed
      H.modify_ (\st -> st {
          pages = Map.singleton 0 zerothPage
        }
      ) 
      params <- H.gets (\st -> st.feedParams)
      void $ tailRecM (fillPreload params feed) 0
      lock <- H.liftAff do
        delay (Milliseconds params.preloadMillis)
        new unit
      H.modify_ (\st -> st { lock = Just lock })
    fillPreload params feed i = do
      if i >= params.preloadedPages
        then pure (Done i)
        else do
          managePreload feed
          pure (Loop (i+1))
handleFeedAction (FeedInsertElement e) = do
  state <- H.get
  H.lift $ onElement e
  let b = findBucket e (Map.union state.preloaded state.pages) 
  H.modify_ (insertIntoPage b)
  H.tell _page b (PageInsert e) 
  where
    insertIntoPage p st = st { pages = Map.alter insertInto p st.pages
                             , preloaded = Map.alter insertInto p st.preloaded
                             }
    insertInto Nothing = Nothing
    insertInto (Just page) = Just (page { elements = A.nub $ A.insertBy feedOrder e page.elements })
 
handleFeedAction (PageOutput (PageHeight {id, height})) = do
  H.modify_ setPageHeight
  where
    setPageHeight st = st { pages = Map.alter setHeight id st.pages
                          , preloaded = Map.alter setHeight id st.preloaded
                          }
    setHeight Nothing = Nothing
    setHeight (Just page) = Just (page { pageHeight = height })
handleFeedAction (PageOutput (PageIntersection page)) = mask do
  feed' <- H.getRef (H.RefLabel "feed")
  flip traverse_ feed' $ \feed -> do  
    st <- H.modify (\st -> execState (stateUpdate (computeUpdate st page)) st) 
    t <- H.liftEffect $ scrollTop feed
    H.liftEffect $ traverse_ (\o -> setScrollTop (t + o) feed) st.update.scroll
    H.modify_ (\s -> s { update = { topLoad: Nothing, bottomLoad: Nothing, scroll: Nothing } })
    flip traverse_ st.update.topLoad $ \kv -> do
      a <- loadPageAbove feed kv.value
      traverse_ (\p -> H.modify_ (\s -> s { preloaded = Map.insert p.id p st.preloaded } )) a
    flip traverse_ st.update.bottomLoad $ \kv -> do
      a <- loadPageBelow feed kv.value
      traverse_ (\p -> H.modify_ (\s -> s { pages = Map.insert p.id p s.pages } )) a

handleFeedAction (PageOutput (PageEmpty i)) = do
  H.modify_ (\st -> st { pages = Map.delete i st.pages })

managePreload :: forall e o m .
                 Feed e m
              => Element -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m Unit
managePreload feed = do
  state <- H.get
  let tooFew = Map.size state.preloaded < state.feedParams.preloadedPages
      tooMany = Map.size state.preloaded > state.feedParams.preloadedPages
  when tooFew do
    let top = maybe (Map.findMin state.pages) Just (Map.findMin state.preloaded)
    a <- join <$> traverse (\kv -> loadPageAbove feed kv.value) top
    traverse_ (\p -> H.modify_ (\st -> st { preloaded = Map.insert p.id p st.preloaded } )) a
  when tooMany do
    H.modify_ (\st -> st { preloaded = maybe st.preloaded
                                            (\kv -> Map.delete kv.key st.preloaded)
                                            (Map.findMin st.preloaded)
                         })

data UpdateF e a =
    TopShift { key :: Int, value :: Page e } a 
  | TopUnshift { key :: Int, value :: Page e } a
  | TopLoad { key :: Int, value :: Page e } a
  | TopDelete { key :: Int, value :: Page e } a 
  | BottomLoad { key :: Int, value :: Page e } a
  | BottomDelete { key :: Int, value :: Page e } a
  | UpdateIntersection PageIntersection a

instance Functor (UpdateF e) where
  map f (TopShift page a) = TopShift page (f a)
  map f (TopUnshift page a) = TopUnshift page (f a)
  map f (TopLoad page a) = TopLoad page (f a)
  map f (TopDelete page a) = TopDelete page (f a)
  map f (BottomLoad page a) = BottomLoad page (f a)
  map f (BottomDelete page a) = BottomDelete page (f a)
  map f (UpdateIntersection page a) = UpdateIntersection page (f a)

type Update e = Free (UpdateF e)

topShift :: forall e. { key :: Int, value :: Page e } -> Update e Unit
topShift page = liftF $ TopShift page unit

topUnshift :: forall e. { key :: Int, value :: Page e } -> Update e Unit
topUnshift page = liftF $ TopUnshift page unit

topLoad :: forall e. { key :: Int, value :: Page e } -> Update e Unit
topLoad page = liftF $ TopLoad page unit

topDelete :: forall e. { key :: Int, value :: Page e } -> Update e Unit
topDelete page = liftF $ TopDelete page unit
 
bottomLoad :: forall e. { key :: Int, value :: Page e } -> Update e Unit
bottomLoad page = liftF $ BottomLoad page unit

bottomDelete :: forall e. { key :: Int, value :: Page e } -> Update e Unit
bottomDelete page = liftF $ BottomDelete page unit

updateIntersection :: forall e. PageIntersection -> Update e Unit
updateIntersection page = liftF $ UpdateIntersection page unit

stateUpdate :: forall e. Update e Unit -> State (FeedState e) Unit
stateUpdate f = do
  modify_ (\st -> st { update = st.update { scroll = Nothing } })
  runFreeM go f
  where
    go (TopShift page a) = do 
      modify_ (\st -> st { 
          pages = Map.insert page.key page.value st.pages 
        , preloaded = Map.delete page.key st.preloaded
        , update = st.update { scroll = Just page.value.pageHeight }
        } )
      pure a
    go (TopUnshift page a) = do
      modify_ (\st -> st { 
          pages = Map.delete page.key st.pages
        , preloaded = Map.insert page.key page.value st.preloaded
        , update = st.update { scroll = Just (-page.value.pageHeight) }
        })
      pure a
    go (TopLoad page a) = do
      modify_ (\st -> st {
          update = if ((\u -> u.key) <$> st.update.topLoad) == Just page.key
                     then st.update { topLoad = Nothing }
                     else st.update { topLoad = Just page }
        })
      pure a
    go (TopDelete page a) = do 
      modify_ (\st -> st {
          preloaded = Map.delete page.key st.preloaded
        , update = st.update { topLoad = Nothing }
        })
      pure a
    go (BottomLoad page a) = do
      modify_ (\st -> st {
          update = if ((\u -> u.key) <$> st.update.bottomLoad) == Just page.key
                     then st.update { bottomLoad = Nothing }
                     else st.update { bottomLoad = Just page }
        })
      pure a
    go (BottomDelete page a) = do 
      modify_ (\st -> st {
          pages = Map.delete page.key st.pages
        , update = st.update { bottomLoad = Nothing }
        })
      pure a 
    go (UpdateIntersection { id, height } a) = do 
      let setIntersection Nothing = Nothing
          setIntersection (Just page) = Just (page { visibleHeight = height })
      modify_ (\st -> st {
          pages = Map.alter setIntersection id st.pages
        })
      pure a
    
computeUpdate :: forall e. FeedState e -> PageIntersection -> Update e Unit
computeUpdate { feedParams, pages, preloaded } page = 
  let notVisible (Tuple _ p) = p.visibleHeight == 0.0 
      extraAbove = A.length $ A.takeWhile notVisible $ Map.toUnfoldable pages
      tooFewAbove = extraAbove < feedParams.hiddenPages
      tooManyAbove = extraAbove > feedParams.hiddenPages
      tooFewPreload = Map.size preloaded < feedParams.preloadedPages 
      tooManyPreload = Map.size preloaded > feedParams.preloadedPages 
      extraBelow = A.length $ A.takeWhile notVisible $ A.reverse $ Map.toUnfoldable pages
      tooFewBelow = extraBelow < feedParams.hiddenPages
      tooManyBelow = extraBelow > feedParams.hiddenPages
   in do
    updateIntersection page
    when (feedParams.enableTop && tooFewAbove) $ traverse_ topShift (Map.findMax preloaded)
    when (feedParams.enableTop && tooManyAbove) $ traverse_ topUnshift (Map.findMin pages)
    when (feedParams.enableTop && tooFewPreload) $ traverse_ topLoad (Map.findMin preloaded)
    when (feedParams.enableTop && tooManyPreload) $ traverse_ topDelete (Map.findMin preloaded)
    when tooFewBelow $ traverse_ bottomLoad (Map.findMax pages)
    when tooManyBelow $ traverse_ bottomDelete (Map.findMax pages)


mask :: forall e o m .
        Feed e m
     => H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m Unit 
     -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m Unit 
mask f = do
  lock <- H.gets (\st -> st.lock)
  traverse_ go lock
  where
    go lock = do
        free <- H.liftAff $ tryTake lock
        when (isJust free) (f *> (H.liftAff $ put unit lock))

loadInitialPage :: forall e o m .
                   Feed e m
                => Element -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m (Page e)
loadInitialPage feed = do
  elements <- loadInitialPageElements
  H.lift $ traverse_ onElement elements
  pure { id: 0
       , elements
       , parent: feed
       , pageHeight: 0.0
       , visibleHeight: 0.0
       }
  where
    loadInitialPageElements = do
      init <- H.gets (\st -> st.feedParams.initialElement)
      params <- H.gets (\st -> st.feedParams)
      below <- H.lift $ feedBelow init
      let source = A.fromFoldable <$> Pipes.toListM (below >-> Pipes.take (params.pageSize - 1))
      cons init <$> (H.liftAff $ runResource source)

loadPageAbove :: forall e o m .
                 Feed e m
              => Element
              -> Page e
              -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m (Maybe (Page e))
loadPageAbove feed page = join <$> traverse loadNextPageUp (head page.elements)
  where
    loadNextPageUp :: e -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m (Maybe (Page e))
    loadNextPageUp element = do
      params <- H.gets (\st -> st.feedParams)
      above <- H.lift $ feedAbove element
      let source = A.fromFoldable <$> Pipes.toListM (above >-> Pipes.take params.pageSize)
      elements <- A.reverse <$> (H.liftAff $ runResource source)
      H.lift $ traverse_ onElement elements
      if null elements
        then pure Nothing
        else pure $ Just { id: page.id - 1
                         , elements
                         , parent: feed
                         , pageHeight: 0.0
                         , visibleHeight: 0.0
                         }

loadPageBelow :: forall e o m .
                 Feed e m
              => Element
              -> Page e
              -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m (Maybe (Page e))
loadPageBelow feed page = join <$> traverse loadNextPageUp (last page.elements)
  where
    loadNextPageUp :: e -> H.HalogenM (FeedState e) (FeedAction e) (FeedSlots e) o m (Maybe (Page e))
    loadNextPageUp element = do
      params <- H.gets (\st -> st.feedParams)
      below <- H.lift $ feedBelow element
      let source = A.fromFoldable <$> Pipes.toListM (below >-> Pipes.take params.pageSize)
      elements <- H.liftAff $ runResource source
      H.lift $ traverse_ onElement elements
      if null elements
        then pure Nothing
        else pure $ Just { id: page.id + 1
                         , elements
                         , parent: feed
                         , pageHeight: 0.0
                         , visibleHeight: 0.0
                         }


     



renderFeed :: forall e m .
              Feed e m
           => FeedState e -> H.ComponentHTML (FeedAction e) (FeedSlots e) m
renderFeed feedState = do
  HH.div
    [ style do
        width (pct 100.0)
        height (pct 100.0)
        overflow hidden
    ]
    [ renderLoaded
    , renderBarrier
    , renderPreloaded
    ]
  where
    renderPageSlot (Tuple i page) = HH.slot _page i pageComponent page PageOutput
    renderLoaded =
      HH.div [ HP.ref (H.RefLabel "feed")
             , style do
                 marginRight (px (-50.0))
                 paddingRight (px 50.0) 
                 height (pct 100.0)
                 overflowY scroll
             ]
             (renderPageSlot <$> Map.toUnfoldable feedState.pages) 
    renderBarrier =
      HH.div [ style do
                 marginRight (px (-50.0))
                 paddingRight (px 50.0) 
                 height (pct 100.0)
                 zIndex (-1)
                 position relative
                 top (pct (-100.0))
             ]
             [
             ]
    renderPreloaded =
      HH.div [ style do
                zIndex (-2)
                position relative
             ]
             (preload <$> Map.toUnfoldable feedState.preloaded)
    preload page@(Tuple i _) =
      HH.div [ style do
                 zIndex ((-2) - (abs i))
                 opacity 0.0
                 position relative
             ]
             [ renderPageSlot page
             ]

type Page e =
  { id :: Int
  , elements :: Array e
  , parent :: Element
  , pageHeight :: Number
  , visibleHeight :: Number
  } 

data PageInsert e a =
  PageInsert e a

data PageAction e =
    InitializePage
  | PageResize (Array ResizeObserverEntry)
  | PageIntersect (Array IntersectionObserverEntry)
  | PageDeleteElement e

type PageIntersection = {
      id :: Int
    , height :: Number
    } 


data PageOutput =
    PageHeight {
      id :: Int
    , height :: Number
    }
  | PageIntersection PageIntersection
  | PageEmpty Int

type PageSlots e = ( pageElement :: forall q o . H.Slot q o e )
_pageElement = Proxy :: Proxy "pageElement"

pageComponent :: forall e m .
                 Feed e m
              => H.Component (PageInsert e) (Page e) PageOutput m
pageComponent =
  H.mkComponent
    { initialState: identity
    , render: renderPage
    , eval: H.mkEval $ H.defaultEval { handleAction = pageAction
                                     , handleQuery = pageInsert
                                     , initialize = Just InitializePage
                                     }
    }
  where
    renderPage page =
      HH.div
        [ HP.ref (H.RefLabel "page")
        , style do
            overflow overflowAuto
        ] 
        ((\e -> HH.slot_ _pageElement e element e) <$> page.elements)

    pageInsert :: forall a . PageInsert e a -> H.HalogenM (Page e) (PageAction e) (PageSlots e) PageOutput m (Maybe a)
    pageInsert (PageInsert e a) = do
       H.modify_ (\st -> st { elements = A.nub $ A.insertBy feedOrder e st.elements })
       pure $ Just a

    pageAction :: PageAction e -> H.HalogenM (Page e) (PageAction e) (PageSlots e) PageOutput m Unit
    pageAction InitializePage = do
       H.getRef (H.RefLabel "page") >>= traverse_ observe
       e <- H.lift feedDelete
       traverse_ (\x -> void $ H.subscribe (PageDeleteElement <$> x)) e
      where
        observe page = observeHeight page *> observeIntersection page
        observeIntersection page = do
          parent <- H.gets (\p -> p.parent)
          { emitter, listener } <- H.liftEffect HS.create
          void $ H.subscribe emitter
          io <- H.liftEffect $ newIntersectionObserver
                                (\a _ -> HS.notify listener (PageIntersect a))
                                (root := parent)
          liftEffect $ WIO.observe io page
        observeHeight page = do
          { emitter, listener } <- H.liftEffect HS.create
          void $ H.subscribe emitter
          ro <- H.liftEffect $ newResizeObserver (\a _ -> HS.notify listener (PageResize a))
          liftEffect $ WRO.observe ro page
    pageAction (PageResize o) = do
      pageId <- H.gets (\page -> page.id)
      let h = sum ((\e -> e.contentRect.height) <$> o)
      H.raise (PageHeight { id: pageId, height: h })
    pageAction (PageIntersect o) = do
      let h = sum ((\e -> e.intersectionRect.height) <$> o)
      pageId <- H.gets (\page -> page.id)      
      H.modify_ (\st -> st { visibleHeight = h})
      H.raise (PageIntersection { id: pageId, height: h })
    pageAction (PageDeleteElement e) = do
      state <- H.modify (\st -> st { elements = A.delete e st.elements })
      when (null state.elements) $ H.raise (PageEmpty state.id)
    
