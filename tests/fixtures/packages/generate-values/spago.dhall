{ name = "generate-values"
, dependencies =
  [ "arrays"
  , "control"
  , "effect"
  , "enums"
  , "foldable-traversable"
  , "gen"
  , "identity"
  , "integers"
  , "lcg"
  , "lists"
  , "maybe"
  , "newtype"
  , "numbers"
  , "partial"
  , "prelude"
  , "tailrec"
  , "transformers"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
