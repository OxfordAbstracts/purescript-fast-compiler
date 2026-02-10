module Elmish.TimeMachine.Formatting.HTML
  ( formatCollapsible
  , formatCollapsibleMessage
  )
  where

import Prelude

import Data.Array as Array
import Data.Foldable (fold)
import Data.Lazy (defer, force)
import Data.Maybe (Maybe(..))
import Data.Monoid (guard)
import Data.String (trim)
import Data.Tuple.Nested ((/\))
import Elmish (ReactElement, (<|))
import Elmish.HTML.Styled as H
import Elmish.Hooks as Hooks
import Elmish.TimeMachine.Formatting (Value(..))
import Elmish.TimeMachine.Formatting as F
import Elmish.TimeMachine.Types.Message (Message(..))

-- | Represents a value as a recursively collapsible component, where each
-- | composite node (ADTs, Records, and Arrays) can be expanded or collapsed
formatCollapsible :: { comma :: Boolean , expanded :: Boolean , parens :: Boolean } -> Value -> ReactElement
formatCollapsible props val = Hooks.component Hooks.do
  nodeExpanded /\ setNodeExpanded <- Hooks.useState props.expanded

  let
    toggleBtn :: ∀ a. _ -> _ a -> _ -> _
    toggleBtn l items r
      | Array.null items =
        H.text $ trim (l <> r) <> guard props.comma ","
      | otherwise =
        H.div "etm-d-inline-flex"
        [ H.button_ "etm-btn etm-icon-btn etm-btn-sm etm-btn-highlight"
            { onClick: setNodeExpanded <| not nodeExpanded }
            if nodeExpanded
              then l <> " ▼"
              else l <> "…" <> r <> " ▶"
        , guard props.comma $
            H.span "" ","
        ]

    content :: ∀ a. _ -> _ a -> (a -> _) -> _
    content r items fmt =
      guardLazy nodeExpanded \_ ->
        H.fragment
        [ H.div "etm-pl-sm" $
            H.div "" <<< fmt <$> items
        , fold $ H.div "" <$> (r <> guard props.comma (Just ","))
        ]

  Hooks.pure case val of
    VCustom tag args ->
      H.fragment
      [ guard (nodeExpanded && parens) $
          H.div "" "("
      , toggleBtn (tag <> " ") args ""
      , content (guard parens $ Just ")") args $
          formatCollapsible { expanded: false, parens: true, comma: false }
      ]
      where
        parens = props.parens && not Array.null args
    VObject obj ->
      H.fragment
      [ toggleBtn "{" obj "}"
      , content (Just "}") obj \{ key, value } ->
          H.div "" $
          [ H.text $ formatKey key
          , H.text ": "
          , formatCollapsible { expanded: false, parens: false, comma: true } value
          ]
      ]
    VArray arr ->
      H.fragment
      [ toggleBtn "[" arr "]"
      , content (Just "]") arr $
          formatCollapsible { expanded: false, parens: false, comma: true }
      ]
    VPrim _ ->
      H.text $
        F.formatValue val <> guard props.comma ","

-- | A collapsible component tailored towards the `Message` type, which first
-- | unwraps the message
formatCollapsibleMessage :: ∀ a. Message a -> ReactElement
formatCollapsibleMessage = case _ of
  Init ->
    H.text "Initial State"
  Message msg ->
    formatCollapsible { expanded: true, parens: false, comma: false } $
      F.toValue msg

formatKey :: Value -> String
formatKey = case _ of
  VCustom tag args -> Array.fold
    [ guard (not Array.null args) "("
    , tag
    , guard (not Array.null args) " …"
    , guard (not Array.null args) ")"
    ]
  VObject _ -> "{…}"
  VArray _ -> "[…]"
  VPrim prim -> F.formatValue $ VPrim prim

guardLazy :: ∀ a. Monoid a => Boolean -> (Unit -> a) -> a
guardLazy p = force <<< guard p <<< defer
