-- A record pun `{ affected_rows }` references the top-level value
-- `affected_rows`. Because that value has no signature, it is only
-- bound after its SCC is inferred — so the SCC dependency graph must
-- include the pun's implicit reference, otherwise `affected_rows` is
-- ordered after `foo` and inference reports UnboundVar.
module Test where

data P = P

bar :: { sel :: { affected_rows :: P } } -> P
bar _ = P

foo :: P
foo = bar { sel: { affected_rows } }

affected_rows = P
