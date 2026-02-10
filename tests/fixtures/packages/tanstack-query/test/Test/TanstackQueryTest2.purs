module Test.TanstackQueryTest where

import Prelude

import Effect.Aff (Milliseconds(..), delay)
import Effect.Aff as Aff
import Effect.Aff.AVar as AVar
import React.TestingLibrary (cleanup, render)
import TanStack.Query (newQueryClient, queryClientProvider)
import Test.UseQueryExample (useQueryExample)
import ViTest (ViTest, afterEach, beforeEach, describe, test, viTest)
import ViTest.Expect ((====))
import ViTest.Expect.DOM (elemText)

main :: ViTest
main = viTest do
  queryClient <- newQueryClient
  describe "The Tanstack Query Bindings" do
    afterEach cleanup
    void $ test "make calls to a fake server" do
        { findByTestId, findByText } <- renderWithClientProvider queryClient $ useQueryExample {
            loadData: do
              Aff.delay (20.0 # Milliseconds)
              pure "I am a fake server response"
        }
        renderedText <- findByTestId "rendered-text" >>= elemText
        renderedText ==== "Loading"
        responseText <- findByText "I am a fake server response" >>= elemText
        responseText ==== "I am a fake server response"
  where
  renderWithClientProvider client x =  render $ queryClientProvider { client } [ x ]
