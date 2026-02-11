{ name = "svg-parser"
, dependencies =
  [ "arrays"
  , "control"
  , "either"
  , "lists"
  , "prelude"
  , "string-parsers"
  , "strings"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
