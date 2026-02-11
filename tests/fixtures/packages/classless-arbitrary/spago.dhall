{ name = "classless-arbitrary"
, dependencies =
  [ "arrays"
  , "classless"
  , "either"
  , "enums"
  , "gen"
  , "heterogeneous"
  , "identity"
  , "lists"
  , "maybe"
  , "partial"
  , "prelude"
  , "quickcheck"
  , "record"
  , "st"
  , "strings"
  , "tuples"
  , "type-equality"
  , "typelevel-prelude"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
