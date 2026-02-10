module Record.Optional.Fields.Errors where

import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Prim.TypeError (Above, Beside, Doc, Quote, QuoteLabel, Text)
import Record.Optional.Fields.Types (AtProp, Context, ErrorDesc, Root, TypeError, UnexpectedType, UnsupportedProp)
import Type.Equality (class TypeEquals)

class RenderErrorContext (ctx :: Context) (doc :: Doc) | ctx -> doc

instance
  ( RenderErrorContext (parent t) above
  , TypeEquals doc
      ( above |>
          Text "- At field `" >> QuoteLabel prop >> Text "`: "
      )
  ) =>
  RenderErrorContext (AtProp parent prop r t) doc

else instance RenderErrorContext (Root r t) (Text "An error occurred while checking input option type:" |> Text "")

infixr 5 type Above as |>

infixr 6 type Beside as >>

class RenderErrorDesc (desc :: ErrorDesc) (doc :: Doc) | desc -> doc

instance
  ( RowToList r rl
  , RenderLabels rl labelsDoc
  ) =>
  RenderErrorDesc (UnsupportedProp prop r)
    ( Text "  Unsupported field name: `" >> QuoteLabel prop >> Text "`."
        |> Text ""
        |> Text "💡 Supported fields include: " >> labelsDoc
    )

instance
  RenderErrorDesc (UnexpectedType a b)
    ( Text "  Unexpected value type: `" >> Quote b >> Text "`"
        |> Text ""
        |> Text "💡 You must specify a value of type `" >> Quote a >> Text "`."
    )

class RenderLabels (rl :: RowList Type) (doc :: Doc) | rl -> doc

instance RenderLabels RL.Nil (Text "There are no available fields.")
else instance RenderLabels (RL.Cons l _1 RL.Nil) (Text "`" >> QuoteLabel l >> Text "`")
else instance
  ( RenderLabels ls rest
  ) =>
  RenderLabels (RL.Cons l _1 ls) (Text "`" >> QuoteLabel l >> Text "` " >> rest)

class RenderError (e :: Type) (doc :: Doc) | e -> doc

instance
  ( RenderErrorContext ctx header
  , RenderErrorDesc desc body
  ) =>
  RenderError (TypeError ctx desc) (header |> body)