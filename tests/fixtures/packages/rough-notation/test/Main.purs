module Test.Main where

import Prelude

import Control.Parallel (parSequence_, parTraverse_, parallel, sequential)
import Data.Array as Array
import Data.Either (either)
import Data.Foldable (for_, traverse_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Int (toNumber)
import Data.Maybe (fromJust)
import Data.Traversable (for, traverse)
import Effect (Effect)
import Effect.Aff (Aff, Milliseconds(..), delay, runAff_, throwError)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Class.Console (logShow)
import Partial.Unsafe (unsafePartial)
import RoughNotation (annotate, hideAnnotation, showAnnotation)
import RoughNotation.Config (BracketType(..), RoughAnnotationType, RoughPadding(..))
import RoughNotation.Config as RoughAnnotationType
import Web.DOM.Element (Element, toEventTarget, toParentNode)
import Web.DOM.Element as Element
import Web.DOM.NodeList as NodeList
import Web.DOM.NonElementParentNode (getElementById)
import Web.DOM.ParentNode (QuerySelector(..), querySelector, querySelectorAll)
import Web.Event.EventTarget (addEventListener, eventListener)
import Web.HTML (window)
import Web.HTML.Event.EventTypes as EventTypes
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.Window (document)


main :: Effect Unit
main = runAff_ (either throwError logShow) $ unsafePartial do
  document <- toNonElementParentNode <$> liftEffect (window >>= document)
  let lookupSection sectionId = fromJust <$> liftEffect (getElementById sectionId document)

  lookupSection "underlineSection" >>= annotateUnderlineSection
  lookupSection "boxSection" >>= annotateBoxSection
  lookupSection "circleSection" >>= annotateCircleSection
  lookupSection "highlightSection" >>= annotateHighlightSection
  lookupSection "strikeSection" >>= annotateStrikeThroughSection
  lookupSection "crossSection" >>= annotateCrossedOffSection
  lookupSection "bracketSection" >>= annotateBracketSection
  lookupSection "multilineSection" >>= annotateMultilineSection
  lookupSection "configSection" >>= annotateConfigSection
  lookupSection "noanimSection" >>= annotateNoAnimationSection

  lookupSection "durationSection" >>= annotateSequenceSection

annotateUnderlineSection :: Partial => Element -> Aff Unit
annotateUnderlineSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "span") (toParentNode section))
  h3     <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  let config = { strokeWidth: 3.0, padding: Padding 3.0, color: "#B71C1C"}
  a1 <- liftAff $ annotate span RoughAnnotationType.Underline config
  a2 <- liftAff $ annotate h3 RoughAnnotationType.Underline config

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)

annotateBoxSection :: Partial => Element -> Aff Unit
annotateBoxSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "span") (toParentNode section))
  h3     <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  let config = { strokeWidth: 2.0, padding: Padding 4.0, color: "#4A148C"}
  a1 <- liftAff $ annotate span RoughAnnotationType.Box config
  a2 <- liftAff $ annotate h3 RoughAnnotationType.Box config

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)



annotateCircleSection :: Partial => Element -> Aff Unit
annotateCircleSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "span") (toParentNode section))
  h3     <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  let config = { padding: Padding 6.0, color: "#0D47A1"}
  a1 <- liftAff $ annotate span RoughAnnotationType.Circle config
  a2 <- liftAff $ annotate h3 RoughAnnotationType.Circle config

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)

annotateHighlightSection :: Partial => Element -> Aff Unit
annotateHighlightSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "span") (toParentNode section))
  h3     <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  let config = { color: "#FFD54F"}
  a1 <- liftAff $ annotate span RoughAnnotationType.Highlight config
  a2 <- liftAff $ annotate h3 RoughAnnotationType.Highlight config

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)


annotateStrikeThroughSection :: Partial => Element -> Aff Unit
annotateStrikeThroughSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "span") (toParentNode section))
  h3     <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  let config = { color: "#1B5E20", strokeWidth: 2.0 }
  a1 <- liftAff $ annotate span RoughAnnotationType.StrikeThrough config
  a2 <- liftAff $ annotate h3 RoughAnnotationType.StrikeThrough config

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)


annotateCrossedOffSection :: Partial => Element -> Aff Unit
annotateCrossedOffSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "span") (toParentNode section))
  h3     <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  let config = { color: "#F57F17", strokeWidth: 2.0 }
  a1 <- liftAff $ annotate span RoughAnnotationType.CrossedOff config
  a2 <- liftAff $ annotate h3 RoughAnnotationType.CrossedOff config

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)

annotateBracketSection :: Partial => Element -> Aff Unit
annotateBracketSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "p.blockp") (toParentNode section))
  h3     <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  a1 <- liftAff $ annotate span RoughAnnotationType.Bracket
          { color: "red"
          , strokeWidth: 2.0
          , padding: FullPadding 2.0 10.0 2.0 10.0
          , brackets: [ Left, Right ]}
  a2 <- liftAff $ annotate h3 RoughAnnotationType.Bracket
          { color: "red"
          , strokeWidth: 2.0, brackets: [Top]}
  let ag = [a1, a2]

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    parTraverse_ hideAnnotation ag
    parTraverse_ showAnnotation ag

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)


annotateMultilineSection :: Partial => Element -> Aff Unit
annotateMultilineSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  mlspan   <- fromJust <$> liftEffect (querySelector (QuerySelector "#mlspan") (toParentNode section))
  let config =  { color: "#ffD54F", animationDuration: Milliseconds 1500.0, multiline: true, iterations: 1 }
  a1 <- liftAff $ annotate mlspan RoughAnnotationType.Highlight config

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    showAnnotation a1

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)

annotateNoAnimationSection :: Partial => Element -> Aff Unit
annotateNoAnimationSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  h3   <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  i   <- fromJust <$> liftEffect (querySelector (QuerySelector "i") (toParentNode section))

  a1 <- annotate h3 RoughAnnotationType.Box { color: "#263238", animate: false }
  a2 <- annotate i RoughAnnotationType.Underline { color: "#263238", strokeWidth: 4.0, animate: false}

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)

annotateConfigSection :: Partial => Element -> Aff Unit
annotateConfigSection section = do
  button <- fromJust <$> liftEffect (querySelector (QuerySelector "button") (toParentNode section))
  h3   <- fromJust <$> liftEffect (querySelector (QuerySelector "h3") (toParentNode section))
  span   <- fromJust <$> liftEffect (querySelector (QuerySelector "span") (toParentNode section))

  a1 <- annotate h3 RoughAnnotationType.Box { color: "#D50000", strokeWidth: 10.0 }
  a2 <- annotate span RoughAnnotationType.Box { color: "#33691E", animationDuration: Milliseconds 3000.0}

  eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
    hideAnnotation a1
    hideAnnotation a2
    parSequence_
      [ showAnnotation a1
      , showAnnotation a2
      ]

  liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)

annotateSequenceSection :: Partial => Element -> Aff Unit
annotateSequenceSection section = do
  let fromNode = fromJust <<< Element.fromNode

  --buttonNodeList <- liftEffect (querySelectorAll (QuerySelector "button") (toParentNode section))
  --[ parallelButton, sequenceButton, reverseButton ] <- liftEffect $ NodeList.toArray buttonNodeList
  [ parallelButton, sequenceButton, reverseButton, staggeredButton ] <- liftEffect (querySelectorAll (QuerySelector "button") (toParentNode section) >>= NodeList.toArray)
  elements <- liftEffect (querySelectorAll (QuerySelector "span") (toParentNode section) >>= NodeList.toArray)
  annotations <- for elements \word ->
    annotate (fromNode word) RoughAnnotationType.Box { color: "#D50000", strokeWidth: 2.0 }

  let
    addOnClickEventListener button action = do
      eventListener <- liftEffect $ eventListener \_ -> runAff_ (\_ -> pure unit) do
        traverse_ hideAnnotation annotations
        action
      liftEffect $ addEventListener EventTypes.click eventListener false (toEventTarget button)

  addOnClickEventListener (fromNode sequenceButton) (traverse_ showAnnotation annotations)
  addOnClickEventListener (fromNode parallelButton) (parTraverse_ showAnnotation annotations)
  addOnClickEventListener (fromNode reverseButton) (traverse_ showAnnotation (Array.reverse annotations))
  addOnClickEventListener (fromNode staggeredButton) $ sequential $
    forWithIndex_ annotations \i a ->
      parallel do
        (delay (Milliseconds (toNumber i * 400.0)))
        showAnnotation a
      
  



