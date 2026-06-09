module Test.Multi.ParallelInitB where

import Test.Multi.ParallelPrelude
import Test.Multi.ParallelInitA (ModelExt)

-- A DIFFERENT module with its own `type PageModel = …` — mirrors
-- AdminDashboard.Pages.EventPage.Model. This collides on the bare
-- name "PageModel" with InitA's alias.

type PageModel =
  { loadable :: Int
  , now :: Int
  , ui :: Int
  }

init :: forall a. ModelExt a -> Aff PageModel
init _ = Aff

data LazyPage = LazyPage

lazyAff :: Aff LazyPage
lazyAff = Aff
