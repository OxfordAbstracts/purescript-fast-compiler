{ name = "eta-conversion"
, license = "MIT"
, repository = "https://github.com/pujoheadsoft/purescript-eta-conversion"
, dependencies =
  [ "aff"
  , "effect"
  , "prelude"
  , "spec"
  , "transformers"
  , "type-equality"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
