{ name = "pirates-charm"
, dependencies =
  [ "aff"
  , "arrays"
  , "effect"
  , "hyrule"
  , "parallel"
  , "prelude"
  , "refs"
  , "st"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
