-- Regression test: a foreign type and a type synonym with the same name
-- should not cause a false "partially applied synonym" error.
--
-- When ForeignNode.Node (foreign, kind Type, arity 0) and
-- SynonymNode.Node (type synonym with 3 params) are both in scope,
-- uses of the foreign Node should not be flagged as a partially applied
-- synonym.
module ForeignTypeSynonymSameName where

import ForeignTypeSynonymSameName.ForeignNode (Node) as DOM
import ForeignTypeSynonymSameName.Reexporter as R

-- Use the foreign Node in a type signature — this should not
-- trigger "Type synonym Node is partially applied"
identity :: DOM.Node -> DOM.Node
identity x = x
