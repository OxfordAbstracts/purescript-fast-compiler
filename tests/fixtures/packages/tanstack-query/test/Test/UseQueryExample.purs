module Test.UseQueryExample where

import Prelude

import Beta.DOM as DOM
import Effect.Aff (Aff, message)
import Effect.Unsafe (unsafePerformEffect)
import Network.RemoteData (RemoteData(..))
import React.Basic (JSX)
import React.Basic.Hooks as React
import TanStack.Query (queryKey, useQuery)

type Props = { loadData :: Aff String }

useQueryExample :: Props -> JSX
useQueryExample = React.element useQueryExampleComponent

useQueryExampleComponent :: React.ReactComponent Props
useQueryExampleComponent = unsafePerformEffect $ React.reactComponent "UseQueryExample" \props -> React.do
  q <- useQuery @String { queryKey: queryKey "the-result", queryFn: props.loadData }
  pure $ DOM.div { "data-testid": "rendered-text" } case q.data of
    NotAsked -> "Not Asked"
    Loading -> "Loading"
    Failure errorMsg -> message errorMsg
    Success result -> result
