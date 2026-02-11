{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "grain-router"
, license = "MIT"
, repository = "https://github.com/purescript-grain/purescript-grain-router"
, dependencies =
  [ "arrays"
  , "control"
  , "effect"
  , "foldable-traversable"
  , "foreign"
  , "grain"
  , "integers"
  , "lists"
  , "maybe"
  , "numbers"
  , "ordered-collections"
  , "prelude"
  , "profunctor"
  , "strings"
  , "tuples"
  , "web-events"
  , "web-html"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
