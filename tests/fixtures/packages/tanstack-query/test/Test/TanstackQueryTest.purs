module Test.TanstackQueryTest2 where

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
    void $ test "catches errors that are thrown in aff" do
        { findByTestId, findByText } <- renderWithClientProvider queryClient $ useQueryExample {
            loadData: do
              Aff.throwError (Aff.error "Fake server error")
        }
        void $ findByText "Fake server error"
  where
  renderWithClientProvider client x =  render $ queryClientProvider { client } [ x ]
