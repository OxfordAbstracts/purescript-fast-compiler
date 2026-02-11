{ name = "yoga-fetch"
, license = "MIT"
, repository = "https://github.com/rowtype-yoga/purescript-yoga-fetch.git"
, dependencies =
  [ "aff"
  , "aff-promise"
  , "arraybuffer-types"
  , "effect"
  , "foreign"
  , "foreign-object"
  , "newtype"
  , "prelude"
  , "typelevel-prelude"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
