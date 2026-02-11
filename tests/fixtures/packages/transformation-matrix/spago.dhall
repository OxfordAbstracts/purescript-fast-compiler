{ name = "transformation-matrix"
, license = "BSD-3-Clause"
, repository = "https://github.com/jstoxrocky/purescript-transformation-matrix"
, dependencies =
  [ "aff"
  , "arrays"
  , "effect"
  , "either"
  , "foldable-traversable"
  , "numbers"
  , "prelude"
  , "spec"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
