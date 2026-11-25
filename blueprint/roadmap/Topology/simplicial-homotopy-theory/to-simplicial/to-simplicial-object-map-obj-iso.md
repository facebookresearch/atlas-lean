# To Simplicial Object map Obj Iso

Postcomposition comparison for the data-to-simplicial transport.

Orientation `(X.toSimplicialObject ⋙ F) ≅ (mapObj F X).toSimplicialObject`.
Both components are identity isomorphisms (`eqToHom` of the object equality);
arbitrary-map naturality is the propositional commutation
`toSimplicialObject_mapObj_map`, proved by GenRel generator induction with
`Functor.map_comp` / `map_id`, not by definitional equality.
