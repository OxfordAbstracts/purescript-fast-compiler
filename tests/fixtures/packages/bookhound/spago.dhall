{ name = "bookhound"
, dependencies =
  [ "arrays"
  , "bifunctors"
  , "control"
  , "either"
  , "foldable-traversable"
  , "integers"
  , "lazy"
  , "lists"
  , "maybe"
  , "numbers"
  , "ordered-collections"
  , "partial"
  , "prelude"
  , "strings"
  , "transformers"
  , "tuples"
  , "unicode"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
, repository = "https://github.com/albertprz/purescript-bookhound"
}
