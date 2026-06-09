module Test.Multi.ParallelMain where

import Test.Multi.ParallelPrelude
import Test.Multi.ParallelModel (Page(..))
import Test.Multi.ParallelInitA as InitA
import Test.Multi.ParallelInitB as InitB

-- Mirrors AdminDashboard.RouteToPage:
--   * `case _ of` with multiple arms, each calling a different
--     module's `init` and wrapping the result in a different Page
--     constructor.
--   * Each arm has TWO `<-` bindings (the actual pattern).
--   * Result type is `Aff { page :: Page, lazy :: LazyPage }`.
data Route = EventRoute | SoaaControlsRoute

routeToPage
  :: forall a
   . InitA.ModelExt a
  -> Route
  -> Aff { page :: Page, lazy :: InitB.LazyPage }
routeToPage model = case _ of
  EventRoute -> sequential ado
    page <- parallel $ model # InitB.init <#> EventPage
    lazy <- parallel InitB.lazyAff
    in { page, lazy }
  SoaaControlsRoute -> sequential ado
    page <- parallel $ model # InitA.init <#> SoaaControlsPage
    lazy <- parallel InitB.lazyAff
    in { page, lazy }
