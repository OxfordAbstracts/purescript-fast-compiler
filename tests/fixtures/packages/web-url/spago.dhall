{ name = "web-url"
, dependencies =
  [ "aff"
  , "effect"
  , "maybe"
  , "partial"
  , "prelude"
  , "spec"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "BSD-3-Clause"
, repository = "https://github.com/mjepronk/purescript-web-url.git"
}
