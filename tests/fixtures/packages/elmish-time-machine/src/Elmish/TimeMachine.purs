module Elmish.TimeMachine
  ( Activity
  , Expanded
  , Keybindings
  , Message
  , defaults
  , withTimeMachine
  , withTimeMachine'
  )
  where

import Prelude

import Data.Foldable (fold, for_)
import Data.Function.Uncurried (Fn2, runFn2)
import Data.Maybe (Maybe(..))
import Data.Monoid (guard)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested ((/\))
import Debug as Debug
import Effect.Aff (Milliseconds(..), delay)
import Effect.Class (liftEffect)
import Elmish (ComponentDef, ReactElement, fork, lmap, subscribe, (<|))
import Elmish.HTML.Styled as H
import Elmish.Hooks as Hooks
import Elmish.Subscription (Subscription(..))
import Elmish.TimeMachine.Formatting as F
import Elmish.TimeMachine.Formatting.HTML as FH
import Elmish.TimeMachine.Types.History (History)
import Elmish.TimeMachine.Types.History as History
import Web.DOM (Element)
import Web.DOM.Document (createElement) as DOM
import Web.DOM.Element as Element
import Web.DOM.Node (appendChild) as DOM
import Web.DOM.NonElementParentNode (getElementById) as W
import Web.Event.EventTarget (addEventListener, eventListener, removeEventListener)
import Web.HTML (window) as W
import Web.HTML.HTMLDocument (body, toDocument, toNonElementParentNode) as W
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window (document) as W
import Web.HTML.Window (toEventTarget)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent as KeyboardEvent
import Web.UIEvent.KeyboardEvent.EventTypes (keydown)

data Message msg
  = Message msg
  -- Controls
  | Undo
  | Redo
  | Jump Int
  | Play
  | Pause
  | Stop
  | Rewind
  | FastForward
  | TimeTravel
  -- UI
  | ToggleExpanded
  | ToggleSection Section
  -- Keydown
  | Keydown KeyboardEvent

type State msg s =
  { history :: History msg s
  , activity :: Activity
  , visible :: Boolean
  , expanded :: Expanded
  , keybindings :: Keybindings
  , playbackDelay :: Number
  }

data Activity
  = Playing
  | Paused
  | Stopped
  | Rewinding
  | FastForwarding
derive instance Eq Activity

data Expanded
  = Expanded (Set Section)
  | Collapsed

data Section
  = Past
  | Present
  | Future
derive instance Eq Section
derive instance Ord Section

-- | A record of keybindings, each represented by a predicate function which
-- | returns true iff a `KeyboardEvent` should trigger the given command
type Keybindings =
  { toggle :: KeyboardEvent -> Boolean
  }

-- | Wraps a `ComponentDef` to add a "time machine" debug tool to the Elmish UI
withTimeMachine ::
  ∀ msg state
  . Debug.DebugWarning
  => ComponentDef msg state
  -> ComponentDef (Message msg) (State msg state)
withTimeMachine =
  withTimeMachine' defaults

-- | Default configuration for keybindings and the amount of delay when
-- | rewinding or fastforwarding through events
defaults :: { keybindings :: Keybindings, playbackDelay :: Number }
defaults =
  { keybindings:
      { toggle: \e ->
          (KeyboardEvent.ctrlKey e || KeyboardEvent.metaKey e) &&
          KeyboardEvent.altKey e &&
          KeyboardEvent.code e == "KeyZ"
     }
  , playbackDelay: 100.0
  }

-- | A version of `withTimeMachine` that allows configuring the keybinding for
-- | showing/hiding the time machine
withTimeMachine' ::
  ∀ msg state
  . Debug.DebugWarning
  => { keybindings :: Keybindings, playbackDelay :: Number }
  -> ComponentDef msg state
  -> ComponentDef (Message msg) (State msg state)
withTimeMachine' { keybindings, playbackDelay } def = { init, update, view }
  where
    init = do
      subscribe Keydown keydownSub
      state <- def.init # lmap Message
      pure
        { history: History.init state
        , activity: Playing
        , visible: true
        , expanded: Collapsed
        , keybindings
        , playbackDelay
        }

    update state = case _ of
      Message msg -> do
        next <- def.update (History.presentState state.history) msg # lmap Message
        let
          track = case state.activity of
            Playing -> History.track
            Paused -> History.stash
            Stopped -> const <<< const
            Rewinding -> const <<< const
            FastForwarding -> const <<< const
        pure state { history = track state.history msg next }
      Undo ->
        pure state { history = History.undo state.history }
      Redo ->
        pure state { history = History.redo state.history }
      Jump index ->
        pure state { history = History.jump index state.history }
      Play ->
        pure state
          { history = History.play state.history
          , activity = Playing
          }
      Pause ->
        pure state { activity = Paused }
      Stop ->
        pure state
          { history = History.stop state.history
          , activity = Stopped
          }
      Rewind -> do
        fork $ pure TimeTravel
        pure state { activity = Rewinding }
      FastForward -> do
        fork $ pure TimeTravel
        pure state { activity = FastForwarding }
      TimeTravel -> do
        let
          activity = case state.activity of
            Rewinding
              | History.hasPast state.history -> state.activity
              | otherwise -> Paused
            FastForwarding
              | History.hasFuture state.history -> state.activity
              | otherwise -> Playing
            _ -> state.activity
        when (activity == Rewinding || activity == FastForwarding) $
          fork do
            delay $ Milliseconds state.playbackDelay
            pure TimeTravel
        pure state
          { history = case activity of
              Rewinding -> History.undo state.history
              FastForwarding -> History.redo state.history
              _ -> state.history
          , activity = activity
          }
      ToggleExpanded ->
        pure state { expanded = toggle state.expanded }
      ToggleSection section | Expanded sections <- state.expanded ->
        pure state { expanded = Expanded $ Set.toggle section sections }
      ToggleSection _ ->
        pure state
      Keydown e | state.keybindings.toggle e ->
        pure state { visible = not state.visible }
      Keydown _ ->
        pure state
      where
        toggle = case _ of
          Expanded _ -> Collapsed
          Collapsed -> Expanded $ Set.singleton Present

    view { history, activity, visible, expanded } dispatch =
      H.fragment
      [ def.view (History.presentState history) $ dispatch <<< Message
      , portal { id: "tardis-time-machine", visible } content
      , stylesheet
      ]
      where
        content =
          H.div_ "etm-container" { tabIndex: -1 }
          [ header
          , body
          ]

        header =
          H.div "etm-header"
          [ whenCollapsed $ undoButton ""
          , H.code "etm-code" $
              F.formatMessage false $
                History.latestMessage history
          , whenCollapsed $ redoButton ""
          , H.button_ "etm-btn etm-ml-auto"
              { onClick: dispatch <| ToggleExpanded
              , disabled: false
              }
              case expanded of
                Expanded _ -> "▼"
                Collapsed -> "▶"
          ]

        body = whenExpanded \sections ->
          H.div "etm-body"
          [ controls
          , section
              { section: Past, expanded: sections, bodyClass: "" } $
              historyEvent <$> History.past history
          , section
              { section: Present, expanded: sections, bodyClass: "etm-px-sm" }
              [ H.h6 "" "Last Message"
              , H.div "etm-code-block" $
                  FH.formatCollapsibleMessage $
                    History.latestMessage history
              , H.h6 "" "Current State"
              , H.div "etm-code-block" $
                  FH.formatCollapsible { expanded: true, parens: false, comma: false } $
                    F.toValue $ History.presentState history
              ]
          , section
              { section: Future, expanded: sections, bodyClass: "" } $
              historyEvent <$> History.future history
          ]

        historyEvent { index, message } =
          H.pre_ "etm-history-event"
            { onClick: dispatch <| Jump index } $
            F.formatMessage true message

        section props c =
          H.div "etm-section"
          [ H.h6_ "etm-section-header"
              { onClick: dispatch <| ToggleSection props.section }
              [ H.div "" case props.section of
                  Past -> "Past"
                  Present -> "Present"
                  Future -> "Future"
              , H.div ""
                  if Set.member props.section props.expanded
                    then "▼"
                    else "▶"
              ]
          , guard (Set.member props.section props.expanded) $
              H.div ("etm-section-body " <> props.bodyClass) c
          ]

        controls =
          H.div "etm-section etm-d-flex etm-p-sm"
          [ undoButton "etm-icon-btn"
          , redoButton "etm-icon-btn"
          , rewindButton
          , playPauseButton
          , stopButton
          , fastForwardButton
          ]

        undoButton className =
          controlButton className
            { title: "Undo"
            , message: Undo
            , disabled: not History.hasPast history
            }
            "↩️"

        redoButton className =
          controlButton className
            { title: "Redo"
            , message: Redo
            , disabled: not History.hasFuture history
            }
            "↪️"

        playPauseButton =
          case activity of
            Playing -> pauseButton
            Paused -> playButton
            Stopped -> playButton
            Rewinding -> pauseButton
            FastForwarding -> pauseButton

        playButton =
          controlButton "etm-icon-btn"
            { title: "Play (Jump to end of history and continue live updates)"
            , message: Play
            , disabled: false
            }
            "▶️"

        pauseButton =
          controlButton "etm-icon-btn"
            { title: "Pause (Stash any future updates)"
            , message: Pause
            , disabled: false
            }
            "⏸️"

        stopButton =
          controlButton "etm-icon-btn"
            { title: "Stop (Stop updates and erase future)"
            , message: Stop
            , disabled: activity == Stopped
            }
            "⏹️"

        rewindButton =
          controlButton "etm-icon-btn etm-ml-auto"
            { title: "Rewind"
            , message: Rewind
            , disabled: activity == Rewinding || not History.hasPast history
            }
            "⏪"

        fastForwardButton =
          controlButton "etm-icon-btn"
            { title: "Fast Forward"
            , message: FastForward
            , disabled: activity == FastForwarding || not History.hasFuture history
            }
            "⏩"

        controlButton className { title, message, disabled } =
          H.button_ ("etm-btn " <> className)
            { onClick: dispatch <| message
            , disabled
            , title
            , "aria-label": title
            }

        whenExpanded f =
          case expanded of
            Expanded sections -> f sections
            Collapsed -> H.empty

        whenCollapsed c =
          case expanded of
            Collapsed -> c
            Expanded _ -> H.empty

    keydownSub = Subscription \dispatch -> liftEffect do
      listener <- eventListener \e -> case KeyboardEvent.fromEvent e of
        Just ke -> dispatch ke
        _ -> pure unit

      W.window <#> toEventTarget >>= addEventListener keydown listener false

      pure $
         liftEffect $ W.window <#> toEventTarget >>= removeEventListener keydown listener false

portal :: { id :: String, visible :: Boolean } -> ReactElement -> ReactElement
portal { id, visible } content = Hooks.component Hooks.do
  container /\ setContainer <- Hooks.useState Nothing

  Hooks.useEffect $ liftEffect do
    document <- W.window >>= W.document
    mContainer <- W.toNonElementParentNode document # W.getElementById id
    case mContainer of
      Just _ ->
        setContainer mContainer
      Nothing -> do
        mBody <- W.body document
        for_ mBody \body -> do
          container' <- DOM.createElement "div" $ W.toDocument document
          Element.setId id container'
          DOM.appendChild (Element.toNode container') (HTMLElement.toNode body)
          setContainer $ Just container'

  Hooks.pure $ guard visible $ fold $
    runFn2 createPortal_ content <$> container

foreign import createPortal_ :: Fn2 ReactElement Element ReactElement

stylesheet :: ReactElement
stylesheet = H.style ""
  """
    div.etm-container {
      position: fixed !important;
      bottom: 1rem !important;
      right: 1rem !important;
      border: 1px solid lightgray !important;
      border-radius: 0.5rem !important;
      background-color: white !important;
      width: 300px !important;
      color: #212529 !important;
      font-family: system-ui, -apple-system, "Segoe UI", Roboto, "Helvetica Neue", Arial, "Noto Sans", "Liberation Sans", sans-serif, "Apple Color Emoji", "Segoe UI Emoji", "Segoe UI Symbol", "Noto Color Emoji" !important;
      line-height: 1.5 !important;
    }

    div.etm-header {
      display: flex !important;
      align-items: center !important;
      padding: 0.75rem !important;
    }

    div.etm-body {
      border-top: 1px solid lightgray !important;
      max-height: 500px !important;
      overflow: auto !important;
    }

    button.etm-btn {
      display: inline-block !important;
      text-align: center !important;
      text-decoration: none !important;
      vertical-align: middle !important;
      cursor: pointer !important;
      background-color: transparent !important;
      border: none !important;
      padding: 0.375rem 0.75rem !important;
      font-size: 1rem !important;
      border-radius: 0.25rem !important;
      margin: 0;
      font-family: inherit;
      line-height: inherit;
    }

    button.etm-btn[disabled] {
      cursor: default !important;
    }

    button.etm-btn.etm-btn-sm {
      font-size: 0.75rem !important;
    }

    button.etm-btn.etm-btn-highlight:hover {
      background-color: #cce7fe !important;
    }

    .etm-ml-auto {
      margin-left: auto !important;
    }

    pre.etm-history-event {
      cursor: pointer !important;
      overflow: hidden !important;
      text-overflow: ellipsis !important;
      margin: 0 !important;
      padding: 0.5rem 0.75rem !important;
      direction: ltr !important;
      unicode-bidi: bidi-override !important;
      white-space: pre !important;
      display: block !important;
      font-size: .875rem !important;
    }

    pre.etm-history-event:hover {
      background-color: #e6f5ff !important;
    }

    div.etm-section {
      border-bottom: 1px solid lightgray !important;
    }

    div.etm-section:last-child {
      border-bottom: none !important;
    }

    .etm-container h6 {
      font-weight: 500 !important;
      line-height: 1.2 !important;
      font-size: 1rem !important;
      margin-top: 0 !important;
      margin-bottom: 0.5rem !important;
    }

    h6.etm-section-header {
      display: flex !important;
      align-items: center !important;
      justify-content: space-between !important;
      margin-bottom: 0 !important;
      cursor: pointer !important;
      padding: 0.75rem !important;
    }

    .etm-p-sm {
      padding: 0.75rem !important;
    }

    .etm-px-sm {
      padding: 0 0.75rem !important;
    }

    .etm-pl-sm {
      padding-left: 0.75rem !important;
    }

    button.etm-btn.etm-icon-btn {
      padding: 0 0.25rem !important;
    }

    pre.etm-code-block, div.etm-code-block {
      white-space: pre !important;
      background-color: #efefef !important;
      padding: 0.75rem 0.5rem !important;
      border: 1px solid lightgray !important;
      border-radius: 0.25rem !important;
      font-family: SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", "Courier New", monospace !important;
      direction: ltr !important;
      unicode-bidi: bidi-override !important;
      display: block !important;
      font-size: .875em !important;
      overflow: auto !important;
      display: block;
      margin-top: 0;
      margin-bottom: 1rem;;
    }

    code.etm-code {
      color: #656565 !important;
      font-family: SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", "Courier New", monospace !important;
      font-size: .875em !important;
      direction: ltr !important;
      unicode-bidi: bidi-override !important;
    }

    .etm-d-flex {
      display: flex !important;
    }

    .etm-d-inline-flex {
      display: inline-flex !important;
    }

    .etm-align-center {
      align-items: center !important;
    }
  """
