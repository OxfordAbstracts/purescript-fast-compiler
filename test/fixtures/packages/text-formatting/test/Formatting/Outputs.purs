module Test.Formatting.Outputs where

import Prelude

import Type.Proxy (Proxy)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Text.Output as O
import Data.Text.Format as F
import Data.Text.Doc as D

import Data.Text.Output.Blessed as O
import Data.Text.Output.Html as O
import Data.Text.Output.Markdown as O
import Data.Text.Output.Org as O

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

import Test.Utils (helper)


options =
    { break : D.All, indent : D.Spaces 2 }


spec :: Spec Unit
spec = do

  describe "Formatting works properly for different outputs" $ do

    helper
        { title : \idx _ -> "Example " <> show idx
        , spec : \(example /\ output)-> do
            O.perform O.blessed options example `shouldEqual` output.blessed
            O.perform O.html options example `shouldEqual` output.html
            O.perform O.markdown options example `shouldEqual` output.markdown
            O.perform O.org options example `shouldEqual` output.org
        }
        outputsExamples


outputsExamples :: Array (F.Tag /\ { html :: String, markdown :: String, blessed :: String, org :: String })
outputsExamples =
    [ F.s "foo" /\
        { html : "foo", markdown : "foo", blessed : "foo", org : "foo" }
    , F.bolds "foo" /\
        { html : "<b>foo</b>", markdown : "**foo**", blessed : "{bold}foo{/bold}", org : "*foo*" }
    , F.code "javascript" "function() { return 42; }" /\
        { html :
            """<code lang="javascript">function() { return 42; }</code>"""
        , markdown :
"""```javascript
function() { return 42; }
```"""
        , blessed :
            "function() { return 42; }"
        , org :
"""#+BEGIN_SRC javascript
function() { return 42; }
#+END_SRC"""
        }
    , F.tableh
        [ F.s "a", F.s "b", F.s "c" ]
        [ F.s <$> [ "1", "4", "7" ]
        , F.s <$> [ "2", "5", "8" ]
        , F.s <$> [ "3", "6", "9" ]
        ] /\
        { html :
"""<table><thead><th>a</th>
<th>b</th>
<th>c</th></thead>
<tr><td>1</td>
<td>4</td>
<td>7</td></tr>
<tr><td>2</td>
<td>5</td>
<td>8</td></tr>
<tr><td>3</td>
<td>6</td>
<td>9</td></tr></table>"""
        , markdown :
"""<table><thead><th>a</th>
<th>b</th>
<th>c</th></thead>
<tr><td>1</td>
<td>4</td>
<td>7</td></tr>
<tr><td>2</td>
<td>5</td>
<td>8</td></tr>
<tr><td>3</td>
<td>6</td>
<td>9</td></tr></table>"""
        , blessed :
"""a|b|c
----------
1|4|7
2|5|8
3|6|9"""
        , org :
"""|a|b|c|
|-+-+-|
|1|4|7|
|2|5|8|
|3|6|9|"""
        }
    ]