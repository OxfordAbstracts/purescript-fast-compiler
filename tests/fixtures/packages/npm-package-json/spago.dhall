{ name = "npm-package-json"
, license = "MIT"
, repository = "https://github.com/maxdeviant/purescript-npm-package-json"
, dependencies =
  [ "argonaut"
  , "control"
  , "either"
  , "foreign-object"
  , "maybe"
  , "ordered-collections"
  , "prelude"
  , "psci-support"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
