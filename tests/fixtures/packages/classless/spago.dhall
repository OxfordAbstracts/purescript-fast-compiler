{ name = "classless"
, dependencies = [ "heterogeneous", "prelude", "record" ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
