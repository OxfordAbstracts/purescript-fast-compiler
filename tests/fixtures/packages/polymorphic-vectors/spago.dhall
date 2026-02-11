{ name = "polymorphic-vectors"
, dependencies =
  [ "distributive"
  , "foldable-traversable"
  , "numbers"
  , "prelude"
  , "record"
  , "safe-coerce"
  , "type-equality"
  , "typelevel-prelude"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
, repository =
    "https://github.com/artemisSystem/purescript-polymorphic-vectors.git"
}
