module ForeignTypeSynonymSameName.SynonymNode where

-- A type synonym also named Node (like Halogen.HTML.Elements.Node)
type Node r w i = Array r -> Array w -> i
