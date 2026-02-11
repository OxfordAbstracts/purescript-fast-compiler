{ name = "which"
, license = "MIT"
, repository = "https://github.com/maxdeviant/purescript-which"
, dependencies =
  [ "arrays"
  , "effect"
  , "foreign"
  , "maybe"
  , "nullable"
  , "options"
  , "prelude"
  , "psci-support"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
