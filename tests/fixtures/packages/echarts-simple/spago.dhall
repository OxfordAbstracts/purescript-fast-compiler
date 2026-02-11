{ name = "echarts-simple"
, dependencies =
  [ "console", "effect", "functions", "prelude", "web-dom" ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "Apache-2.0"
, repository = "https://github.com/lucasdicioccio/purescript-echarts-simple"
}
