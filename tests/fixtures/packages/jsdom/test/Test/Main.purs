module Test.Main where

import Data.Maybe (Maybe(..), isJust, maybe)
import Prelude

import Control.Monad.Error.Class (throwError)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Console (log)
import Effect.Exception (error)
import JSDOM as JSDOM
import Test.Assert (assert)
import Web.DOM (Node)
import Web.DOM.Document as Web.DOM.Document
import Web.DOM.Node as Web.DOM.Node
import Web.HTML.HTMLElement as Web.HTML.HTMLElement

firstText :: Node -> Effect (Maybe String)
firstText node = Web.DOM.Node.firstChild node >>= traverse Web.DOM.Node.textContent

exampleHTML :: String
exampleHTML = "<p>hogeika</p>"

exampleURI :: String
exampleURI = "http://www.nicovideo.jp/"

main :: Effect Unit
main = do
  log "Testing jsdom"

  (jsdomDocument :: Web.DOM.Document.Document) <-
    JSDOM.jsdom exampleHTML JSDOM.defaultConstructorOptions
      >>= JSDOM.window
      >>= JSDOM.document

  (pNode :: Web.DOM.Node.Node) <-
    Web.DOM.Node.firstChild (Web.DOM.Document.toNode jsdomDocument)
      >>= maybe (throwError $ error "pNode not found") pure

  text <- firstText $ Web.DOM.Document.toNode jsdomDocument
  assert $ text == Just "hogeika"

  log "Testing jsdom config"

  (uri :: String) <-
    JSDOM.jsdom exampleHTML (JSDOM.defaultConstructorOptions { url = exampleURI })
      >>= JSDOM.window
      >>= JSDOM.document
      >>= Web.DOM.Document.documentURI

  assert $ uri == exampleURI

  assert $ isJust $ Web.HTML.HTMLElement.fromNode pNode
