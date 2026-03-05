module Component where

-- A module that defines `data Model` — a data type, not a type alias.
-- When another module imports this AND defines its own `type Model = ...` alias,
-- the local alias must still expand correctly (not be blocked by con_zero_blockers).

data Model = Init | Ready String

render :: Model -> String
render Init = "loading"
render (Ready s) = s
