module BenchLib.Reporters.Html
  ( Color
  , LineStyle
  , Opts
  , reportHtml
  , reportHtml_
  ) where

import Prelude

import BenchLib (Reporter, SuiteResult, defaultReporter)
import BenchLib.Reporters.Json (codecSuiteResult)
import Data.Argonaut as Json
import Data.Codec.Argonaut (JsonCodec)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Record as CAR
import Data.String (Pattern(..))
import Data.String as Str
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Traversable (foldl)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS

type Opts =
  { lineStyles :: Array LineStyle
  , filePath :: String
  }

type LineStyle =
  { color :: Color
  , opacity :: Number
  , width :: Number
  }

type Color =
  { r :: Int
  , g :: Int
  , b :: Int
  }

defaultOpts :: Opts
defaultOpts =
  { lineStyles:
      [ { color: { r: 255, g: 99, b: 132 }, opacity, width }
      , { color: { r: 54, g: 162, b: 235 }, opacity, width }
      , { color: { r: 153, g: 102, b: 255 }, opacity, width }
      , { color: { r: 255, g: 159, b: 64 }, opacity, width }
      , { color: { r: 255, g: 99, b: 132 }, opacity, width }
      , { color: { r: 54, g: 162, b: 235 }, opacity, width }
      , { color: { r: 255, g: 206, b: 86 }, opacity, width }
      , { color: { r: 75, g: 192, b: 192 }, opacity, width }
      , { color: { r: 153, g: 102, b: 255 }, opacity, width }
      , { color: { r: 255, g: 159, b: 64 }, opacity, width }
      ]
  , filePath: "bench-results.html"
  }
  where
  opacity = 0.5
  width = 2.0

writeHtml :: Opts -> SuiteResult -> Effect Unit
writeHtml opts suiteResults = do
  let
    config =
      { lineStyles: opts.lineStyles
      , data: suiteResults
      }

  let jsonStr = Json.stringifyWithIndent 2 $ CA.encode codecConfig config

  let
    replacements =
      [ { regex: unsafeRegex "{{title}}" noFlags
        , replacement: suiteResults.suiteName
        }
      , { regex: unsafeRegex "(/\\* config start \\*/)([\\s\\S]*)(/\\* config end \\*/)" noFlags
        , replacement: "$1\n" <> (indent "      " ("const config = " <> jsonStr)) <> "\n" <> "      $3"
        }
      ]

  let out = foldl (\acc { regex, replacement } -> Regex.replace regex replacement acc) template replacements
  FS.writeTextFile UTF8 opts.filePath out

reportHtml :: (Opts -> Opts) -> Reporter
reportHtml mkOpts =
  let
    opts = mkOpts defaultOpts
  in
    defaultReporter
      { onSuiteFinish = \suiteResults -> liftEffect do
          writeHtml opts suiteResults
          Console.log ("Wrote HTML report to " <> opts.filePath)
      }

reportHtml_ :: Reporter
reportHtml_ = reportHtml identity

indent :: String -> String -> String
indent indentStr str = Str.split (Pattern pat) str # map (indentStr <> _) # Str.joinWith pat
  where
  pat = "\n"

type Config =
  { lineStyles :: Array LineStyle
  , data :: SuiteResult
  }

codecConfig :: JsonCodec Config
codecConfig = CAR.object "Config"
  { lineStyles: CA.array codecLineStyle
  , data: codecSuiteResult
  }

codecLineStyle :: JsonCodec LineStyle
codecLineStyle = CAR.object "LineStyle"
  { color: codecColor
  , opacity: CA.number
  , width: CA.number
  }

codecColor :: JsonCodec Color
codecColor = CAR.object "Color"
  { r: CA.int
  , g: CA.int
  , b: CA.int
  }

template :: String
template = """
<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>{{title}}</title>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <style>
      body {
        font-family: Arial, sans-serif;
        margin: 0;
        padding: 0;
      }
      h1 {
        margin: 0;
        padding: 0;
        padding-bottom: 20px;
      }
      h2 {
        margin: 0;
        padding: 0;
        padding-bottom: 10px;
      }
    </style>
  </head>

  <body>
    <script>
      /* config start */
      const config = {
        lineStyles: [
          { color: { r: 255, g: 99, b: 132 }, width: 2, opacity: 0.5 },
          { color: { r: 54, g: 162, b: 235 }, width: 2, opacity: 0.5 },
          { color: { r: 255, g: 206, b: 86 }, width: 2, opacity: 0.5 },
        ],
        transparencies: [0.5],
        data: {
          suiteName: "Sample Bench Suite",
          groups: [
            {
              groupName: "Add item to front",
              benchs: [
                {
                  benchName: "Array.cons",
                  size: 1,
                  duration: 0.1,
                },
                {
                  benchName: "Array.cons",
                  size: 2,
                  duration: 0.2,
                },
                {
                  benchName: "Array.cons",
                  size: 3,
                  duration: 0.3,
                },
                {
                  benchName: "List.cons",
                  size: 1,
                  duration: 0.2,
                },
                {
                  benchName: "List.cons",
                  size: 2,
                  duration: 0.4,
                },
                {
                  benchName: "List.cons",
                  size: 3,
                  duration: 0.6,
                },
              ],
            },
            {
              groupName: "Add item to end",
              benchs: [
                {
                  benchName: "Array.snoc",
                  size: 1,
                  duration: 0.1,
                },
                {
                  benchName: "Array.snoc",
                  size: 2,
                  duration: 0.2,
                },
                {
                  benchName: "Array.snoc",
                  size: 3,
                  duration: 0.3,
                },

                {
                  benchName: "List.snoc",
                  size: 1,
                  duration: 0.2,
                },
                {
                  benchName: "List.snoc",
                  size: 2,
                  duration: 0.4,
                },
                {
                  benchName: "List.snoc",
                  size: 3,
                  duration: 0.6,
                },
              ],
            },
          ],
        },
      };
      /* config end */

      function renderCharts(dataConfig) {
        const container = document.createElement("div");
        container.style.maxWidth = "600px";
        container.style.margin = "0 auto";
        container.style.padding = "20px";

        const header = document.createElement("h1");
        header.textContent = dataConfig.suiteName;
        container.appendChild(header);

        document.body.appendChild(container);

        dataConfig.groupResults.forEach((group, groupIndex) => {
          const chartContainer = document.createElement("div");
          chartContainer.style.marginBottom = "40px";

          const title = document.createElement("h2");
          title.textContent = group.groupName;
          chartContainer.appendChild(title);

          const canvas = document.createElement("canvas");
          canvas.id = `chart-${groupIndex}`;
          chartContainer.appendChild(canvas);

          container.appendChild(chartContainer);

          const labels = [
            ...new Set(
              group.benchResults.flatMap((bench) =>
                bench.samples.map((sample) => sample.size)
              )
            ),
          ];

          const datasets = group.benchResults.map((bench, index) => {
            const style = config.lineStyles[index % config.lineStyles.length];
            const rgbaColor = `rgba(${style.color.r}, ${style.color.g}, ${style.color.b}, ${style.opacity})`;

            return {
              label: bench.benchName,
              data: bench.samples.map((sample) => ({
                x: sample.size,
                y: sample.average,
              })),
              borderColor: rgbaColor,
              borderWidth: style.width,
              backgroundColor: rgbaColor,
              fill: false,
              tension: 0.1,
            };
          });

          new Chart(canvas.getContext("2d"), {
            type: "line",
            data: {
              labels: labels,
              datasets: datasets,
            },
            options: {
              responsive: true,
              plugins: {
                legend: {
                  display: true,
                },
              },
              scales: {
                x: {
                  type: "linear",
                  title: {
                    display: true,
                    text: "Input Size",
                  },
                },
                y: {
                  max: (ctx) => {
                    const maxValue = Math.max(
                      ...ctx.chart.data.datasets.flatMap((ds) => ds.data.map((d) => d.y))
                    );
                    console.log(ctx.chart.data.datasets);
                    return Math.max(maxValue, 10);
                  },
                  min: 0,
                  title: {
                    display: true,

                    text: "Average Time (ms)",
                  },
                },
              },
            },
          });
        });
      }

      renderCharts(config.data);
    </script>
  </body>
</html>
"""