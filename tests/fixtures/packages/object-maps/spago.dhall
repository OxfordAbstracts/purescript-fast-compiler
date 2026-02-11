{ name = "object-maps"
, dependencies =
  [ "argonaut-codecs"
  , "argonaut-core"
  , "either"
  , "foldable-traversable"
  , "foreign-object"
  , "maybe"
  , "prelude"
  , "profunctor-lenses"
  , "st"
  , "tuples"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
