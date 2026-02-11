module Test.Main where

import Prelude
import Router (makeRoute, makeRouter, route)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Test.Assert (assert)

main :: Effect Unit
main = do
  testRouteMatch
  testFallback
  testParseParams

testRouteMatch :: Effect Unit
testRouteMatch = do
  let
    route1 = makeRoute "/apples" [ "GET" ]

    router =
      makeRouter
        (Map.fromFoldable [ Tuple route1 (\_req _ctx -> "Hello!") ])
        ("Not Found")
        (\_req -> "/apples")
        (\_req -> "GET")
        (\_req -> {})

    resp = route router ""
  assert $ resp == "Hello!"

testFallback :: Effect Unit
testFallback = do
  let
    route1 = makeRoute "/apples" [ "GET" ]

    router =
      makeRouter
        (Map.fromFoldable [ Tuple route1 (\_req _ctx -> "Hello!") ])
        ("Not Found")
        (\_req -> "/not-apples")
        (\_req -> "GET")
        (\_req -> {})

    resp = route router ""
  assert $ resp == "Not Found"

testParseParams :: Effect Unit
testParseParams = do
  let
    route1 = makeRoute "/apples/:appleId/monkey/:monkeyId" [ "GET" ]

    router =
      makeRouter
        ( Map.fromFoldable
            [ Tuple route1
                ( \_req ctx ->
                    (fromMaybe "" $ Map.lookup "appleId" ctx.params) <> (fromMaybe "" $ Map.lookup "monkeyId" ctx.params)
                )
            ]
        )
        ("Not Found")
        (\_req -> "/apples/1234/monkey/5678")
        (\_req -> "GET")
        (\_req -> {})

    resp = route router ""
  assert $ resp == "12345678"
