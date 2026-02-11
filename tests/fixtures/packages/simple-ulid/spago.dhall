{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "simple-ulid"
, license = "MIT"
, repository = "https://github.com/oreshinya/purescript-simple-ulid"
, dependencies =
  [ "arrays"
  , "datetime"
  , "effect"
  , "exceptions"
  , "integers"
  , "now"
  , "numbers"
  , "prelude"
  , "strings"
  , "tailrec"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
